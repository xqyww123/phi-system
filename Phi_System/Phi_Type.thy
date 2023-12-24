text \<open>
TODO: "is separation" -> component-wise composition 
      "hierarchical composition in sense of functors"



title:
       A New Dimension of Composition towards More Scalable Verification on Separation Logic

abstract:

Scalable verification of concrete program is the pressing difficulty blocking wider application
of the field in industry.
Data Refinement (DR) is a cure to relate concretion and abstraction.
We present a variant of the logic of Bunched Implication (BI) which unifies DR and predicate, where
predicates are assigned with an interpretation of data refinement, so predicates in SL can be
studied from a DR perspective and our theory on DR gives an automation on any 'meaningful' (to this
interpretation) SL predicates.

Our logic provides a new dimension of composition for data refinement along with hierarchical levels of
data structures -- higher order predicates are functors of data refinement (e.g., List) which combines
the refinement of elements (e.g., Int) and yields the refinement of the entire data structure (e.g., List(Int)).
Constructing, destructing, and conversion between refinements are mechanized in a synthetic way over
the hierarchical composition. Key algebraic properties are identified to instantiate the automation,
which are general enough to enable the automation on almost any data structures (involving no first-class
functions nor co-inductive constructs in the paper).
Strategies to derive the properties are given, together with heuristics guessing the form of the properties from definitions.
So, high degree of automation is achieved. Our case studies show the capability of automating
refinement of challenging data structures down to C semantics.


<Other notes>:

When the refinement relations of all parties of a program are identical, a verification is easy and
proof obligations can be extracted on the abstract domain provided by the refinement.
The difficulty lies in constructing / destructing refinements between layers of abstraction, and
converting 

------------------------

The work closest to us is by Dinsdale et al, who try to bring hierarchical composition into data refinement
on specific data structures.
However, it lacks of a general meta theory and a general automation over any data structures like us.
They failed to give the meta theory because they chose wrong formalization, whereas ours thanking to
the unification of DR and predicates, can express it simply using the language of higher order predicates.



The mechanized reasoning is able to solve stratified transformations where any refinement operator (type operator)
\<open>F\<close> that requires a shift between hierarchical layers like \<open>F (G T) \<longrightarrow> G (F T)\<close> must be able to be normalized
into a form where no shift is required, so that the reasoning can solve the transformation layer by layer
recursively, e.g., \<open>F\<^sub>1 \<longrightarrow> G\<^sub>1\<close>, \<open>F\<^sub>2 \<longrightarrow> G\<^sub>2\<close>, ... recursively til \<open>T \<rightarrow> U\<close> for \<open>F\<^sub>1 (F\<^sub>2 (\<dots>(T))) \<rightarrow> G\<^sub>1 (G\<^sub>2 (\<dots>(U)))\<close>.

The shift between layers is commutativity of the type operator.
We believe most of type operators for substantial data structures (that do have some representation in physical memory)
are non-commutative, and commutative operators are closer to specificational logic connectives like modalities,
such as the permission modality (specifying whether do we have total share of a memory reference so we can write to it),
finite multiplicative quantifier, domainoid operator (elucidated later) which are the only commutative operators occurring in our case studies and
that we can imagine. As they are closer to logic connectives, we require specific strategy to be given
and do not provide a general automation.

Among stratified transformations, we support the transformation between \<open>F(T)\<close> and \<open>G(U)\<close> when,
\<^item> \<open>F = G\<close> and the related algebraic properties (transformation functor, separation homomorphism) are given on \<open>F\<close>
\<^item> \<open>F = F\<^sub>a\<close> and \<open>G = F\<^sub>b\<close> are one kind of semimodule type operator of scalars \<open>a, b\<close> respectively, and
  the related properties are given.


If any refinement operator (type operator)










------------------------

title:
            Three Pigs: A Synthetic Approach to Data Refinement, an Algebra of Predicates,
                    and a General Automation for Data Structures, on BI
\<close>

theory Phi_Type
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

text \<open>Guessing Strategy:

\<^item> For non-recursive \<phi>-types and property parameters about booleans (conditions or predicates),
  such as the domain of the identity-elements, we can leave the parameter to be a fixed variable and
  send it to derivers (if the deriving process does not depends on a specific choice of the parameter).
  The derivers would report proof obligations containing the variable, from which we can infer
  an optimal instantiation (either the strongest or the weakest, depending on the property) that the
  variable can be when it does not strengthen the entire proof obligation (i.e., not makes the proof
  problem harder). If so, the result is optimal when the deriving is complete (i.e., yielding the
  weakest proof obligation entailing the property), because the instantiation embeds the most information
  that it can have.

  This strategy usually works well in our case studies, though the optimal instantiation is not always
  inferrable syntactically so we use suboptimal one with heuristics (given where?), and another problem is
  sometime (percentage?) the instantiation may contain too much trivial details and our simplifier
  (provided from the underlying proof assistant) fails to reduce it into a (one of the) simplest form. In
  these cases, manual annotations are given based on the guessed results, so the guessing is still helpful.

\<^item> If the abstract algebra is defined from Bounded Natural Functor (e.g., its logic type is defined
  as an algebraic datatype in most of modern proof assistants), the operators such as mappers,
  predicators, and relators can be hopefully good candidates of the property parameters. This heuristic
  covers recursive \<phi>-types and works well for \<phi>-types modelling ordinary data structures.

\<^item> The candidates guessed above can be in addition constrained or augmented by inference over the syntactic
  expression of the \<phi>-type definition, carried out by the ad-hoc reasoning rules specifying
  the \<phi>-type operators occurring in the expression.
  \<open>T \<s>\<u>\<b>\<j> P \<triangleq> \<lambda>x. (x \<Ztypecolon> T) \<and> P\<close> is an example giving a boolean constraint \<open>P\<close> that can constrain the
  domain of \<open>identity-element\<close>.
  The rules of the syntactic inference are given manually mainly for \<phi>-type embedding of logic connectives.
\<close>


text \<open> Strategy of deriving:

  Essentially the properties are derived from that of existing \<phi>-types, and the initial rules
  of primitive \<phi>-types including vertical composition (\<open>\<Zcomp>\<close>), function and relation embedding (\<open>\<phi>Fun\<close> and \<open>\<phi>Rel\<close>),
  and \<phi>-type embedding of logic connectives,
  are either derived from reasoning over logic connectivities, or manually proven by unfolding
  \<phi>-type colons down to raw predicates.
\<close>

text \<open>
It is true there exists a type theory for which our \<phi>-type logic is a semantic interpretation of it,
where, semantic interpretation \<open>\<lbrakk> x \<rbrakk>\<^sub>T \<equiv> {c : c \<Turnstile> x \<Ztypecolon> T}\<close> assigns (the evaluation of) a term \<open>x\<close> of type \<open>T\<close> to a set of
semantic representations, which for instance can be the set of binary encoding to which the evaluation of term \<open>x\<close> can be compiled;
\<open>\<lbrakk> x : T \<rbrakk> \<equiv> \<lbrakk> x \<rbrakk>\<^sub>T \<noteq> {} \<equiv> \<exists>c. c \<Turnstile> x \<Ztypecolon> T\<close> assigns the semantics of typing judgement,
meaning term \<open>x\<close> is of type \<open>T\<close> iff its evaluation has some semantic representation \<open>c\<close>
(e.g. the evaluation of \<open>x\<close> can be compiled to some binary encoding \<open>c\<close>);
terms of different types can share common semantic representations, \<open>\<lbrakk> x \<rbrakk>\<^sub>T \<inter> \<lbrakk> y \<rbrakk>\<^sub>T\<close> can be non-empty;
at last, a new judgement \<open>x : T \<longrightarrow> y : U\<close> is introduced between two typing judgements,
\<open>\<lbrakk> x : T \<longrightarrow> y : U \<rbrakk> \<equiv> \<lbrakk> x \<rbrakk>\<^sub>T \<subseteq> \<lbrakk> y \<rbrakk>\<^sub>U\<close>, meaning the semantic representations of \<open>x\<close> are included in \<open>y\<close>,
so the semantic is unchanged or relaxed when we replace a covariant \<open>x : T\<close> in a program with \<open>y : U\<close> or
a contravariant \<open>y : U\<close> with \<open>x : T\<close>, if no type error occurs.
The judgement is an extended sub-typing where the term changes for semantic consistency (relaxation),
so may be called as semantical subtyping, the one preserving the semantics of terms versus normal subtyping
preserving the syntactic term.
\<close>



text \<open>

Real data structures are hierarchical, as composition of abstract data types each of which gives a stratified layer.
So are \<phi>-types, as composition of \<phi>-type operators corresponding to each ADT.
We present a stratified ToA reasoning strategy, which peels \<phi>-type operators layer by layer, on both
of the source and the target assertion simultaneously.
On each layer, we transform the source \<phi>-type operator to the target operator, and once they reach
an agreement, by means of the transformation functor we enter their operands which are the inner layers.

It implies the source and the target \<phi>-type should have identical stratified layers.
It is true in real data structures, because if they are composed by difference layers of ADT, they are
essentially different objects. However, in \<phi>-types, not all \<phi>-types characterizes a substantial data
structure but can be (embeddings of) logic connectives or specificational modalities or modifiers,
such as the remark of sharing permission \<open>\<odiv>\<close>.
Though substantial \<phi>-types characterizing a physical data structure are almost certainly non-commutative,
the modalities can be commutative over the stratified layers, because they are essentially
logic connectives.

Particularly when a commutative modality is an associative and scalar-distributive semimodule, troubles come.
The ToA reasoning of the scalar-remarked modalities (\<open>x \<Ztypecolon> F a T * others \<longrightarrow> y \<Ztypecolon> F b U\<close>, with \<open>a \<le> b\<close>) has two directions,
one looking for the missed scalar portion \<open>(b/a)\<close> from the inner layer \<open>T\<close>, reducing to \<open>T \<longrightarrow> F (b/a) U\<close>, 
another looking horizontally from its neighbor \<open>others\<close>, reducing to \<open>others \<longrightarrow> F (b-a) U\<close>.
Even worse, the two reduction can be arithmetically mixed, \<open>T \<longrightarrow> F c U\<close> and \<open>others \<longrightarrow> F d U\<close> such that
\<open>a * c + d = b\<close>.

To reduce the search space, such associative modalities usually demand specific heuristics,
because their commutativity over type operators can be various. However, we propose a conjuncture,
the modalities are either commutative over most of logic connectives and a lot of substantial \<phi>-types,
or of little commutativity over certain logic connectives and barely no substantial \<phi>-types.
Sadly, we cannot verify this conjuncture because associative modalities are uncommon, and most of them
are specific to the inference system. We can only come up with
and encounter in our case studies two associative modalities, operator of permission sharing \<open>n \<odiv> T\<close>
and finite multiplicative quantifier \<open>x\<^sub>i \<Ztypecolon> \<big_ast> dom T \<equiv> \<big_ast> i\<in>dom. x\<^sub>i \<Ztypecolon> T \<close>, (except those already having
specific reasoning heuristics so no need for a general reasoning strategy, e.g., \<open>\<S>\<close>).
The two modalities correspond respectively to the two cases in our conjuncture.

Based on our conjuncture, we come up with a general strategy where we apply a normalization before
the reasoning, by pushing the modalities to the leaves of the syntax tree of a \<phi>-type
(i.e., towards the innermost layers) to collect the modalities all together so that the later reasoning only
needs to consider the scalar distributivity by looking from the neighbors horizontally.
We push them to the leaves because scalar-parameterized modalities are easier to swap over a multi-arity
type operator \<open>F\<^sub>a(G(T,U)) \<longrightarrow> G(F\<^sub>a(T),F\<^sub>a(U))\<close> but not easily back \<open>a = b \<Longrightarrow> G(F\<^sub>a(T),F\<^sub>b(U)) \<longrightarrow> F\<^sub>a(G(T,U))\<close>
which usually requires the scalars of the operands of the multi-arity type operator are equal.

When there are multiple kinds of modalities, we push the modalities of better commutativity (in terms of
the range of type operators that they can swap over into) farther towards leaves, i.e.,
we assign them a order to arrange them in order before the leaves. It introduces a strong assumption
where the commutativity of the modalities can be linearly ordered --- the set of type operators that
a modality of a stronger commutativty can swap over into, is a superset of that of a weaker commutativity.

Certainly, this general strategy is limited due to the strong assumption, but covers any meaningful
modalities that we meet and can imagine.
Again, we recall associative and and scalar-distributive semimodule \<phi>-type operators are usually
modalities tightly bound to the inference system, which usually demands specific heuristics so our
general strategy can only cover little.

\<close>

text \<open>\Concl:

In the domain of data refinement, we found a synthetic method with efficient automation.

From the broader perspective of BI logic, we have re-interpreted the semantics of stateful predicates
(to distinguish with boolean predicates) on BI by relating them to data refinement.
By assuming the predicates are organized meaningfully and structurally, we show, an efficient and
general automation over a lot of data structures can actually be given under such interpretation.

\<close>

text \<open>
int c = (a + b + d);

\<open>int t1 = a + b;
 int c = t1 + d;\<close>

free conversion between \<phi>-types <-> fictions
  impredicativeness 

'a BI  :=  'a set
'a BI  :=  ('a \<times> step-index) set  ,   step-index := nat


semantic models <-| fictions <-|-> \<phi>-types

Hash-table |-> fictions

Array 

\<^item> *synthetic approach* towards conventional data refinement -> automatic algorithm
\<^item> *new dimension* of composition of data refinement -- hierarchical dimension -- functors of data refinement and
    their transformations -> automatic algorithm & more levels of composition
\<^item> automatic algorithm for transformations
    \<^item> identify key properties (transformation functor, separation homomorphism, semimodule ...)
      from which a reasoning algorithm can be instantiated
    \<^item> derive automatically the properties from definitions of \<phi>-types
    \<^item> guess the expression of the properties by various means, such as Natural Bounded Functor (the major
      tool used to define algebraic datatype in modern proof assitants)
\<^item> first fully-automated verification on some algorithm (like quicksort) down to C semantics
  automated verification about Hash-table to C semantics

Scalability is determined by level of composition. We give 1. new level of dimension, 2. automation over 
that dimension

 they don't use functors, so no composition
    List(T) -> List(U)
    we : T -> U
    conventional : List(T) -> List(U)
\<close>


chapter \<open>The Algebra of \<open>\<phi>\<close>-Type\<close>

section \<open>Algebraic Properties of \<phi>-Types\<close>

subsection \<open>Auxiliary Preliminaries\<close>

subsubsection \<open>Conditioned Operators\<close>

definition cond_splitR ("?\<^sub>s\<^sub>R") \<comment> \<open>conditioned module split at right\<close>
  where \<open>?\<^sub>s\<^sub>R C f = (if C then f else (\<lambda>x. (x, unspec))) \<close>

definition cond_splitL ("?\<^sub>s\<^sub>L") \<comment> \<open>conditioned module split at left\<close>
  where \<open>?\<^sub>s\<^sub>L C f = (if C then f else (\<lambda>x. (unspec, x))) \<close>

abbreviation cond_splitR' ("?\<^sub>s\<^sub>R[_]" [30] 1000)
  where \<open>?\<^sub>s\<^sub>R[C] \<equiv> ?\<^sub>s\<^sub>R (LPR_ctrl C)\<close>

abbreviation cond_splitL' ("?\<^sub>s\<^sub>L[_]" [30] 1000)
  where \<open>?\<^sub>s\<^sub>L[C] \<equiv> ?\<^sub>s\<^sub>L (LPR_ctrl C)\<close>

lemma cond_split_red[simp, \<phi>safe_simp]:
  \<open>?\<^sub>s\<^sub>R True f = f\<close>
  \<open>?\<^sub>s\<^sub>R False f = (\<lambda>x. (x, unspec))\<close>
  \<open>?\<^sub>s\<^sub>L True g = g\<close>
  \<open>?\<^sub>s\<^sub>L False g = (\<lambda>x. (unspec, x))\<close>
  unfolding cond_splitR_def cond_splitL_def
  by simp_all


definition cond_unionR ("?\<^sub>j\<^sub>R") \<comment> \<open>conditioned module split at right\<close>
  where \<open>?\<^sub>j\<^sub>R C f = (if C then f else fst) \<close>

definition cond_unionL ("?\<^sub>j\<^sub>L") \<comment> \<open>conditioned module split at left\<close>
  where \<open>?\<^sub>j\<^sub>L C f = (if C then f else snd) \<close>

abbreviation cond_unionR' ("?\<^sub>j\<^sub>R[_]" [30] 1000)
  where \<open>?\<^sub>j\<^sub>R[C] \<equiv> ?\<^sub>j\<^sub>R (LPR_ctrl C)\<close>

abbreviation cond_unionL' ("?\<^sub>j\<^sub>L[_]" [30] 1000)
  where \<open>?\<^sub>j\<^sub>L[C] \<equiv> ?\<^sub>j\<^sub>L (LPR_ctrl C)\<close>

lemma cond_union_red[simp, \<phi>safe_simp]:
  \<open>?\<^sub>j\<^sub>R True f = f\<close>
  \<open>?\<^sub>j\<^sub>R False f = fst\<close>
  \<open>?\<^sub>j\<^sub>L True g = g\<close>
  \<open>?\<^sub>j\<^sub>L False g = snd\<close>
  unfolding cond_unionR_def cond_unionL_def
  by simp_all

lemma cond_union_simp[simp, \<phi>safe_simp]:
  \<open>?\<^sub>j\<^sub>R C fst = fst\<close>
  unfolding LPR_ctrl_def cond_unionR_def
  by simp_all


definition cond_func :: \<open>bool \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)\<close> ("?\<^sub>f")
  where \<open>?\<^sub>f C f = (if C then f else (\<lambda>_. unspec))\<close>

abbreviation cond_func' ("?\<^sub>f[_]" [30] 1000)
  where \<open>?\<^sub>f[C] \<equiv> ?\<^sub>f (LPR_ctrl C)\<close>

lemma cond_func_red[simp, \<phi>safe_simp]:
  \<open>?\<^sub>f True f = f\<close>
  \<open>?\<^sub>f False f = (\<lambda>_. unspec)\<close>
  unfolding cond_func_def
  by simp_all

definition cond_mapper :: \<open>bool \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd)
                                \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd)\<close> ("?\<^sub>M")
  where \<open>?\<^sub>M C m = (if C then m else (\<lambda>_ _. unspec))\<close>

abbreviation cond_mapper' ("?\<^sub>M[_]" [30] 1000)
  where \<open>?\<^sub>M[C] \<equiv> ?\<^sub>M (LPR_ctrl C)\<close>

lemma cond_mapper_red[simp, \<phi>safe_simp]:
  \<open>?\<^sub>M True m = m\<close>
  \<open>?\<^sub>M False m f = (\<lambda>_. unspec)\<close>
  unfolding cond_mapper_def
  by simp_all

lemma cond_mapper_simp[simp, \<phi>safe_simp]:
  \<open>?\<^sub>M C (\<lambda>_ _. unspec) = (\<lambda>_ _. unspec)\<close>
  unfolding LPR_ctrl_def cond_mapper_def
  by simp_all

paragraph \<open>mapToA_assign_id\<close>

lemma [\<phi>reason %mapToA_assign_id+10]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] C
\<Longrightarrow> mapToA_assign_id (m f)
\<Longrightarrow> mapToA_assign_id (?\<^sub>M C m f) \<close>
  unfolding mapToA_assign_id_def Premise_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason %mapToA_assign_id+20]:
  \<open> mapToA_assign_id (m f)
\<Longrightarrow> mapToA_assign_id (?\<^sub>M[True] m f) \<close>
  unfolding mapToA_assign_id_def Premise_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason %mapToA_assign_id+30 for \<open>mapToA_assign_id (?\<^sub>M _ _ _ :: unit \<Rightarrow> unit)\<close>
                                        \<open>mapToA_assign_id (?\<^sub>M[False] _ _ :: ?'a \<Rightarrow> ?'a)\<close>,
       \<phi>reason %mapToA_assign_id    for \<open>mapToA_assign_id (?\<^sub>M _ _ _ :: ?'a \<Rightarrow> ?'a)\<close>]:
  \<open>mapToA_assign_id (?\<^sub>M C m f :: unit \<Rightarrow> unit) \<close>
  unfolding mapToA_assign_id_def
  by (clarsimp simp: fun_eq_iff)

lemma [\<phi>reason %lookup_a_mapper]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] C
\<Longrightarrow> IDE_CP_Reasoning2.lookup_a_mapper (m f) x y
\<Longrightarrow> IDE_CP_Reasoning2.lookup_a_mapper (?\<^sub>M C m f) x y \<close>
  unfolding IDE_CP_Reasoning2.lookup_a_mapper_def Premise_def \<r>Guard_def
  by simp

lemma [\<phi>reason %lookup_a_mapper+10]:
  \<open> IDE_CP_Reasoning2.lookup_a_mapper (m f) x y
\<Longrightarrow> IDE_CP_Reasoning2.lookup_a_mapper (?\<^sub>M[True] m f) x y \<close>
  unfolding IDE_CP_Reasoning2.lookup_a_mapper_def
  by simp

lemma [\<phi>reason %lookup_a_mapper+10]:
  \<open> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] y' : y
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> y' = unspec
\<Longrightarrow> IDE_CP_Reasoning2.lookup_a_mapper (?\<^sub>M[False] m f) x y \<close>
  unfolding IDE_CP_Reasoning2.lookup_a_mapper_def Premise_def Simplify_def
  by simp



subsubsection \<open>Objectize HOL Type-Class Judgement\<close>

text \<open>in order to coordinate commutative and non-commutative model algebras (to support both of them
  in one rule), we use a very tricky method where we objectize HOL type-class judgement
  (\<^const>\<open>class.ab_semigroup_mult\<close>) and decide type-class assertion at reasoning runtime.
\<close>

declare Groups.ab_semigroup_mult_class.ab_semigroup_mult_axioms[\<phi>reason %cutting]

lemma swap_\<phi>Cond_Ins_by_raw_class[no_atp]:
  \<open> if C\<^sub>W then class.ab_semigroup_mult ( (*) :: 'c option BI \<Rightarrow> 'c option BI \<Rightarrow> 'c option BI) else True
\<Longrightarrow> (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) * A = A * (w \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W) \<close>
  for A :: \<open>'c::sep_semigroup option BI\<close>
  apply (cases C\<^sub>W; simp)
  subgoal premises prems
    using ab_semigroup_mult.mult_commute[OF prems(1)] . .


subsubsection \<open>Conditioned Zip \& Unzip\<close>

definition cond_zip ("?\<^sub>Z")
  where \<open>?\<^sub>Z C z mapper = (if C then z else mapper (\<lambda>x. (x, unspec)) o fst)\<close>

definition cond_zip_dom ("?\<^sub>Z\<^sub>D")
  where \<open>?\<^sub>Z\<^sub>D C D D' R' = (if C then D else {x. \<forall>a. a \<in> D' (fst x) \<longrightarrow> (a, unspec) \<in> R' (fst x)})\<close>

definition cond_unzip ("?\<^sub>U\<^sub>Z")
  where \<open>?\<^sub>U\<^sub>Z C uz mapper = (if C then uz else (\<lambda>x. (mapper fst x, unspec)))\<close>

definition cond_unzip_dom ("?\<^sub>U\<^sub>Z\<^sub>D")
  where \<open>?\<^sub>U\<^sub>Z\<^sub>D C D' R' = (if C then UNIV else {x. \<forall>(a,b) \<in> D' x. a \<in> R' x})\<close>


abbreviation cond_zip' ("?\<^sub>Z[_]" [30] 1000)
  where \<open>?\<^sub>Z[C] \<equiv> ?\<^sub>Z (LPR_ctrl C)\<close>

abbreviation cond_zip_dom' ("?\<^sub>Z\<^sub>D[_]" [30] 1000)
  where \<open>?\<^sub>Z\<^sub>D[C] \<equiv> ?\<^sub>Z\<^sub>D (LPR_ctrl C)\<close>

abbreviation cond_unzip' ("?\<^sub>U\<^sub>Z[_]" [30] 1000)
  where \<open>?\<^sub>U\<^sub>Z[C] \<equiv> ?\<^sub>U\<^sub>Z (LPR_ctrl C)\<close>

abbreviation cond_unzip_dom' ("?\<^sub>U\<^sub>Z\<^sub>D[_]" [30] 1000)
  where \<open>?\<^sub>U\<^sub>Z\<^sub>D[C] \<equiv> ?\<^sub>U\<^sub>Z\<^sub>D (LPR_ctrl C)\<close>



paragraph \<open>Basic Rules\<close>

lemma cond_zip_red[simp, \<phi>safe_simp]:
  \<open> ?\<^sub>Z True z mapper = z \<close>
  \<open> ?\<^sub>Z False z mapper = mapper (\<lambda>x. (x, unspec)) o fst \<close>
  unfolding cond_zip_def
  by simp_all

lemma cond_zip_dom_red[simp, \<phi>safe_simp]:
  \<open> ?\<^sub>Z\<^sub>D True D D' R' = D \<close>
  \<open> ?\<^sub>Z\<^sub>D False D D' R' = {x. \<forall>a. a \<in> D' (fst x) \<longrightarrow> (a, unspec) \<in> R' (fst x)} \<close>
  unfolding cond_zip_dom_def
  by simp_all

lemma cond_unzip_red[simp, \<phi>safe_simp]:
  \<open> ?\<^sub>U\<^sub>Z True uz m = uz \<close>
  \<open> ?\<^sub>U\<^sub>Z False uz m x = (m fst x, unspec) \<close>
  unfolding cond_unzip_def
  by simp_all

lemma cond_unzip[simp, \<phi>safe_simp]:
  \<open> fst (uz x) = m fst x
\<Longrightarrow> fst (?\<^sub>U\<^sub>Z flag uz m x) = m fst x \<close>
  unfolding cond_unzip_def
  by clarsimp

lemma cond_unzip_dom_red[simp, \<phi>safe_simp]:
  \<open> ?\<^sub>U\<^sub>Z\<^sub>D True D' R' = UNIV \<close>
  \<open> ?\<^sub>U\<^sub>Z\<^sub>D False D' R' = {x. \<forall>(a,b) \<in> D' x. a \<in> R' x} \<close>
  unfolding cond_unzip_dom_def
  by simp_all

lemma cond_unzip_dom_simp[simp, \<phi>safe_simp]:
  \<open> ?\<^sub>U\<^sub>Z\<^sub>D C (\<lambda>_. {}) R' = UNIV \<close>
  \<open> ?\<^sub>U\<^sub>Z\<^sub>D C D' (\<lambda>_. UNIV) = UNIV \<close>
  unfolding cond_unzip_dom_def
  by simp_all

lemma cond_zip_dom_simp[simp, \<phi>safe_simp]:
  \<open> ?\<^sub>Z\<^sub>D C UNIV (\<lambda>_. {}) R' = UNIV \<close>
  \<open> ?\<^sub>Z\<^sub>D C UNIV D' (\<lambda>_. UNIV) = UNIV \<close>
  \<open> x \<in> ?\<^sub>Z\<^sub>D C D D' (\<lambda>_. UNIV) \<longleftrightarrow> (C \<longrightarrow> x \<in> D) \<close>
  \<open> x \<in> ?\<^sub>Z\<^sub>D C D (\<lambda>_. {}) R' \<longleftrightarrow> (C \<longrightarrow> x \<in> D) \<close>
  unfolding cond_zip_dom_def
  by simp_all



subsubsection \<open>Separatable Mapping\<close> \<comment> \<open>those used in transformation mapper\<close>

definition separatable_unzip
  where \<open>separatable_unzip z uz D\<^sub>u m m\<^sub>1 m\<^sub>2 f g \<longleftrightarrow>
          (\<forall>x\<in>D\<^sub>u. z (map_prod (m\<^sub>1 f) (m\<^sub>2 g) (uz x)) = m (map_prod f g) x) \<close>

definition separatable_cond_unzip
  where \<open>separatable_cond_unzip C z uz D\<^sub>u m m\<^sub>1 m\<^sub>2 f g \<longleftrightarrow>
          ((\<not>C \<longrightarrow> g = (\<lambda>_. unspec)) \<longrightarrow> separatable_unzip z uz D\<^sub>u m m\<^sub>1 m\<^sub>2 f g)\<close>

definition separatable_zip
  where \<open>separatable_zip uz z D\<^sub>z m m\<^sub>1 m\<^sub>2 f g \<longleftrightarrow>
          (\<forall>x\<in>D\<^sub>z. uz (m (map_prod f g) (z x)) = map_prod (m\<^sub>1 f) (m\<^sub>2 g) x)\<close>

definition separatable_cond_zip
  where \<open>separatable_cond_zip C uz z D\<^sub>z m m\<^sub>1 m\<^sub>2 f g \<longleftrightarrow>
          ((\<not>C \<longrightarrow> g = (\<lambda>_. unspec)) \<longrightarrow> separatable_zip uz z D\<^sub>z m m\<^sub>1 m\<^sub>2 f g)\<close>

definition compositional_mapper
  where \<open>compositional_mapper m\<^sub>1 m\<^sub>2 m\<^sub>3 D f g \<longleftrightarrow>
          (\<forall>x \<in> D. m\<^sub>1 f (m\<^sub>2 g x) = m\<^sub>3 (f o g) x)\<close>

definition domain_of_inner_map
  where \<open>domain_of_inner_map mapper D\<^sub>i \<longleftrightarrow>
          (\<forall>f g x. (\<forall>a \<in> D\<^sub>i x. f a = g a) \<longrightarrow> mapper f x = mapper g x)\<close>

definition domain_by_mapper
  where \<open>domain_by_mapper D' m D f D\<^sub>x \<longleftrightarrow> (\<forall>x\<in>D\<^sub>x. D' (m f x) \<subseteq> f ` D x)\<close>

definition separatable_module_zip
  where \<open>separatable_module_zip flag d a b c uz' z' uz z D f g f' g' \<longleftrightarrow>
            (\<forall>x. D x ((f \<otimes>\<^sub>f g o uz c b o z a d) x) \<longrightarrow>
                 (if flag then dabc_equation d a b c else dabc_equation b c d a) \<longrightarrow>
                 (uz' a d o z' c b o f \<otimes>\<^sub>f g o uz c b o z a d) x = (f' \<otimes>\<^sub>f g') x)\<close>


definition module_mapper\<^sub>2\<^sub>2
  where \<open>module_mapper\<^sub>2\<^sub>2 flag d a b c sp' jn' sp jn D\<^sub>s\<^sub>p' D\<^sub>j\<^sub>n' D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D\<^sub>M f\<^sub>c f\<^sub>b f\<^sub>a f\<^sub>d \<longleftrightarrow>
    (\<forall>x. D\<^sub>M x \<longrightarrow>
         (if flag then dabc_equation d a b c else dabc_equation b c d a) \<longrightarrow>
         (let (x\<^sub>a,x\<^sub>d) = x
            ; (x\<^sub>c,x\<^sub>b) = sp c b (jn a d (x\<^sub>a,x\<^sub>d))
            ; (y\<^sub>c,y\<^sub>b) = (f\<^sub>c x\<^sub>c, f\<^sub>b x\<^sub>b)
            ; (y\<^sub>a,y\<^sub>d) = sp' a d (jn' c b (y\<^sub>c,y\<^sub>b))
           in (y\<^sub>a,y\<^sub>d) = (f\<^sub>a x\<^sub>a, f\<^sub>d x\<^sub>d) \<and>
              D\<^sub>j\<^sub>n a d (x\<^sub>a,x\<^sub>d) \<and>
              D\<^sub>s\<^sub>p c b (jn a d (x\<^sub>a,x\<^sub>d)) \<and>
              D\<^sub>j\<^sub>n' c b (y\<^sub>c,y\<^sub>b) \<and>
              D\<^sub>s\<^sub>p' a d (jn' c b (y\<^sub>c,y\<^sub>b))
))\<close>

definition module_mapper\<^sub>1\<^sub>3\<^sub>C
  where \<open>module_mapper\<^sub>1\<^sub>3\<^sub>C C\<^sub>c C\<^sub>d d a da c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f\<^sub>c f g \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow>
         ?\<^sub>+ True da = ?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True a \<and> (C\<^sub>c \<longrightarrow> da ##\<^sub>+ c) \<and> (C\<^sub>d \<longrightarrow> d ##\<^sub>+ a) \<longrightarrow>
         (let (x\<^sub>a,x\<^sub>d,x\<^sub>c) = x
            ; y = f (?\<^sub>j\<^sub>L C\<^sub>c (jn c da) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (jn a d) (x\<^sub>a, x\<^sub>d)))
            ; (y\<^sub>c,y\<^sub>d\<^sub>a) = ?\<^sub>s\<^sub>L C\<^sub>c (sp c da) y
            ; (y\<^sub>a,y\<^sub>d) = ?\<^sub>s\<^sub>R C\<^sub>d (sp a d) y\<^sub>d\<^sub>a
           in g x = ?\<^sub>j\<^sub>L C\<^sub>c (jn c da) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (jn a d) (x\<^sub>a, x\<^sub>d)) \<and>
              (y\<^sub>a,y\<^sub>d,y\<^sub>c) = (f\<^sub>a x\<^sub>a, f\<^sub>d x\<^sub>d, f\<^sub>c x\<^sub>c) \<and>
              (C\<^sub>d \<longrightarrow> D\<^sub>j\<^sub>n a d (x\<^sub>a, x\<^sub>d) \<and>
                      D\<^sub>s\<^sub>p a d y\<^sub>d\<^sub>a) \<and>
              (C\<^sub>c \<longrightarrow> D\<^sub>j\<^sub>n c da (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (jn a d) (x\<^sub>a, x\<^sub>d)) \<and>
                      D\<^sub>s\<^sub>p c da y)))\<close>

definition module_mapper\<^sub>1\<^sub>3
  where \<open>module_mapper\<^sub>1\<^sub>3 d a c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f\<^sub>c f g \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow>
         d+a ##\<^sub>+ c \<and> d ##\<^sub>+ a \<longrightarrow>
         (let (x\<^sub>a,x\<^sub>d,x\<^sub>c) = x
            ; y = f (jn c (d+a) (x\<^sub>c, jn a d (x\<^sub>a, x\<^sub>d)))
            ; (y\<^sub>c,y\<^sub>d\<^sub>a) = sp c (d+a) y
            ; (y\<^sub>a,y\<^sub>d) = sp a d y\<^sub>d\<^sub>a
           in g x = jn c (d+a) (x\<^sub>c, jn a d (x\<^sub>a, x\<^sub>d)) \<and>
              (y\<^sub>a,y\<^sub>d,y\<^sub>c) = (f\<^sub>a x\<^sub>a, f\<^sub>d x\<^sub>d, f\<^sub>c x\<^sub>c) \<and>
              D\<^sub>j\<^sub>n a d (x\<^sub>a, x\<^sub>d) \<and> D\<^sub>s\<^sub>p a d y\<^sub>d\<^sub>a \<and>
              D\<^sub>j\<^sub>n c (d+a) (x\<^sub>c, jn a d (x\<^sub>a, x\<^sub>d)) \<and> D\<^sub>s\<^sub>p c (d+a) y))\<close>

definition module_mapper\<^sub>1\<^sub>2\<^sub>L
  where \<open>module_mapper\<^sub>1\<^sub>2\<^sub>L d a sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow>
         d ##\<^sub>+ a \<longrightarrow>
         (let (x\<^sub>a,x\<^sub>d) = x
            ; y = f (jn a d (x\<^sub>a, x\<^sub>d))
            ; (y\<^sub>a,y\<^sub>d) = sp a d y
           in (y\<^sub>a,y\<^sub>d) = (f\<^sub>a x\<^sub>a, f\<^sub>d x\<^sub>d) \<and>
              D\<^sub>j\<^sub>n a d (x\<^sub>a, x\<^sub>d) \<and> D\<^sub>s\<^sub>p a d y))\<close>

definition module_mapper\<^sub>1\<^sub>2\<^sub>R
  where \<open>module_mapper\<^sub>1\<^sub>2\<^sub>R a c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>a f\<^sub>c f \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow>
         a ##\<^sub>+ c \<longrightarrow>
         (let (x\<^sub>a,x\<^sub>c) = x
            ; y = f (jn c a (x\<^sub>c, x\<^sub>a))
            ; (y\<^sub>c,y\<^sub>a) = sp c a y
           in (y\<^sub>a,y\<^sub>c) = (f\<^sub>a x\<^sub>a, f\<^sub>c x\<^sub>c) \<and> D\<^sub>j\<^sub>n c a (x\<^sub>c, x\<^sub>a) \<and> D\<^sub>s\<^sub>p c a y))\<close>

definition module_mapper\<^sub>3\<^sub>1\<^sub>C
  where \<open>module_mapper\<^sub>3\<^sub>1\<^sub>C C\<^sub>c C\<^sub>d c b db d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow>
         (?\<^sub>+ True db = ?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True b) \<and> (C\<^sub>c \<longrightarrow> db ##\<^sub>+ c) \<and> (C\<^sub>d \<longrightarrow> d ##\<^sub>+ b) \<longrightarrow>
             (let (x\<^sub>c, x\<^sub>d\<^sub>b) = ?\<^sub>s\<^sub>L C\<^sub>c (sp c db) x
                ; (x\<^sub>b, x\<^sub>d) = ?\<^sub>s\<^sub>R C\<^sub>d (sp b d) x\<^sub>d\<^sub>b
               in g x = (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<and>
                  (((?\<^sub>j\<^sub>L C\<^sub>c (jn c db) o apsnd (?\<^sub>j\<^sub>R C\<^sub>d (jn b d))) o
                    (f\<^sub>c \<otimes>\<^sub>f f \<otimes>\<^sub>f f\<^sub>d) o
                    (apsnd (?\<^sub>s\<^sub>R C\<^sub>d (sp b d)) o ?\<^sub>s\<^sub>L C\<^sub>c (sp c db))) x = f' x) \<and>
                  (C\<^sub>d \<longrightarrow> D\<^sub>j\<^sub>n b d (f x\<^sub>b, f\<^sub>d x\<^sub>d) \<and> D\<^sub>s\<^sub>p b d x\<^sub>d\<^sub>b) \<and>
                  (C\<^sub>c \<longrightarrow> D\<^sub>j\<^sub>n c db (f\<^sub>c x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (jn b d) (f x\<^sub>b, f\<^sub>d x\<^sub>d)) \<and>
                          D\<^sub>s\<^sub>p c db x)))\<close>

definition module_mapper\<^sub>3\<^sub>1
  where \<open>module_mapper\<^sub>3\<^sub>1 c b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow> (let (x\<^sub>c, x\<^sub>d\<^sub>b) = sp c (d+b) x
                    ; (x\<^sub>b, x\<^sub>d) = sp b d x\<^sub>d\<^sub>b
                   in g x = (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<and>
                      (((jn c (d+b) o apsnd (jn b d)) o
                        (f\<^sub>c \<otimes>\<^sub>f f \<otimes>\<^sub>f f\<^sub>d) o
                        (apsnd (sp b d) o sp c (d+b))) x = f' x) \<and>
                      D\<^sub>j\<^sub>n b d (f x\<^sub>b, f\<^sub>d x\<^sub>d) \<and> D\<^sub>s\<^sub>p b d x\<^sub>d\<^sub>b \<and>
                      D\<^sub>j\<^sub>n c (d+b) (f\<^sub>c x\<^sub>c, jn b d (f x\<^sub>b, f\<^sub>d x\<^sub>d)) \<and>
                      D\<^sub>s\<^sub>p c (d+b) x))\<close>

definition module_mapper\<^sub>2\<^sub>1\<^sub>R
  where \<open>module_mapper\<^sub>2\<^sub>1\<^sub>R c b sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f' \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow> (let (x\<^sub>c, x\<^sub>b) = sp c b x
                   in ((jn c b o f\<^sub>c \<otimes>\<^sub>f f o sp c b) x = f' x) \<and>
                      D\<^sub>j\<^sub>n c b (f\<^sub>c x\<^sub>c, f x\<^sub>b) \<and>
                      D\<^sub>s\<^sub>p c b x))\<close>

definition module_mapper\<^sub>2\<^sub>1\<^sub>L
  where \<open>module_mapper\<^sub>2\<^sub>1\<^sub>L b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f' \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow>
         d ##\<^sub>+ b \<longrightarrow>
        (let (x\<^sub>b, x\<^sub>d) = sp b d x
          in ((jn b d o f \<otimes>\<^sub>f f\<^sub>d o sp b d) x = f' x) \<and>
             D\<^sub>j\<^sub>n b d (f x\<^sub>b, f\<^sub>d x\<^sub>d) \<and> D\<^sub>s\<^sub>p b d x))\<close>

definition module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C
  where \<open>module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C C\<^sub>c C\<^sub>d c \<epsilon> d\<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow>
         (?\<^sub>+ True d\<epsilon> = ?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True \<epsilon>) \<and> (C\<^sub>c \<longrightarrow> d\<epsilon> ##\<^sub>+ c) \<and> (C\<^sub>d \<longrightarrow> d ##\<^sub>+ \<epsilon>) \<longrightarrow>
         (let (x\<^sub>c, x\<^sub>d\<^sub>\<epsilon>) = ?\<^sub>s\<^sub>L C\<^sub>c (sp c d\<epsilon>) x
            ; (x\<^sub>\<epsilon>, x\<^sub>d) = ?\<^sub>s\<^sub>R C\<^sub>d (sp \<epsilon> d) x\<^sub>d\<^sub>\<epsilon>
           in g x = (x\<^sub>c, e\<^sub>\<epsilon> x\<^sub>\<epsilon>, x\<^sub>d) \<and>
              (((?\<^sub>j\<^sub>L C\<^sub>c (jn c d\<epsilon>) o apsnd (?\<^sub>j\<^sub>R C\<^sub>d (jn \<epsilon> d))) o
                (f\<^sub>c \<otimes>\<^sub>f (i\<^sub>\<epsilon> o f o e\<^sub>\<epsilon>) \<otimes>\<^sub>f f\<^sub>d) o
                (apsnd (?\<^sub>s\<^sub>R C\<^sub>d (sp \<epsilon> d)) o ?\<^sub>s\<^sub>L C\<^sub>c (sp c d\<epsilon>))) x = f' x) \<and>
              D\<^sub>\<epsilon>\<^sub>E x\<^sub>\<epsilon> \<and> D\<^sub>\<epsilon>\<^sub>I (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)) \<and>
              (C\<^sub>d \<longrightarrow> D\<^sub>j\<^sub>n \<epsilon> d (i\<^sub>\<epsilon> (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)), f\<^sub>d x\<^sub>d) \<and> D\<^sub>s\<^sub>p \<epsilon> d x\<^sub>d\<^sub>\<epsilon>) \<and>
              (C\<^sub>c \<longrightarrow> D\<^sub>j\<^sub>n c d\<epsilon> (f\<^sub>c x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (jn \<epsilon> d) (i\<^sub>\<epsilon> (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)), f\<^sub>d x\<^sub>d)) \<and>
                      D\<^sub>s\<^sub>p c d\<epsilon> x)))\<close>

definition module_mapper\<^sub>3\<^sub>\<epsilon>
  where \<open>module_mapper\<^sub>3\<^sub>\<epsilon> c \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow> (let (x\<^sub>c, x\<^sub>d\<^sub>\<epsilon>) = sp c (d+\<epsilon>) x
                    ; (x\<^sub>\<epsilon>, x\<^sub>d) = sp \<epsilon> d x\<^sub>d\<^sub>\<epsilon>
                   in g x = (x\<^sub>c, e\<^sub>\<epsilon> x\<^sub>\<epsilon>, x\<^sub>d) \<and>
                      (((jn c (d+\<epsilon>) o apsnd (jn \<epsilon> d)) o
                        (f\<^sub>c \<otimes>\<^sub>f (i\<^sub>\<epsilon> o f o e\<^sub>\<epsilon>) \<otimes>\<^sub>f f\<^sub>d) o
                        (apsnd (sp \<epsilon> d) o sp c (d+\<epsilon>))) x = f' x) \<and>
                      D\<^sub>\<epsilon>\<^sub>E x\<^sub>\<epsilon> \<and> D\<^sub>\<epsilon>\<^sub>I (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)) \<and>
                      D\<^sub>j\<^sub>n \<epsilon> d (i\<^sub>\<epsilon> (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)), f\<^sub>d x\<^sub>d) \<and> D\<^sub>s\<^sub>p \<epsilon> d x\<^sub>d\<^sub>\<epsilon> \<and>
                      D\<^sub>j\<^sub>n c (d+\<epsilon>) (f\<^sub>c x\<^sub>c, jn \<epsilon> d (i\<^sub>\<epsilon> (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)), f\<^sub>d x\<^sub>d)) \<and>
                      D\<^sub>s\<^sub>p c (d+\<epsilon>) x))\<close>


definition module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R
  where \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R c \<epsilon> sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f' g \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow> (let (x\<^sub>c, x\<^sub>\<epsilon>) = sp c \<epsilon> x
                   in g x = (x\<^sub>c, e\<^sub>\<epsilon> x\<^sub>\<epsilon>) \<and>
                      ((jn c \<epsilon> o f\<^sub>c \<otimes>\<^sub>f (i\<^sub>\<epsilon> o f o e\<^sub>\<epsilon>) o sp c \<epsilon>) x = f' x) \<and>
                      D\<^sub>\<epsilon>\<^sub>E x\<^sub>\<epsilon> \<and> D\<^sub>\<epsilon>\<^sub>I (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)) \<and>
                      D\<^sub>j\<^sub>n c \<epsilon> (f\<^sub>c x\<^sub>c, i\<^sub>\<epsilon> (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>))) \<and>
                      D\<^sub>s\<^sub>p c \<epsilon> x))\<close>

definition module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L
  where \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f' g \<longleftrightarrow>
    (\<forall>x. D x \<longrightarrow>
         d ##\<^sub>+ \<epsilon> \<longrightarrow>
         (let (x\<^sub>\<epsilon>, x\<^sub>d) = sp \<epsilon> d x
           in g x = (e\<^sub>\<epsilon> x\<^sub>\<epsilon>, x\<^sub>d) \<and>
              ((jn \<epsilon> d o (i\<^sub>\<epsilon> o f o e\<^sub>\<epsilon>) \<otimes>\<^sub>f f\<^sub>d o sp \<epsilon> d) x = f' x) \<and>
              D\<^sub>\<epsilon>\<^sub>E x\<^sub>\<epsilon> \<and> D\<^sub>\<epsilon>\<^sub>I (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)) \<and>
              D\<^sub>j\<^sub>n \<epsilon> d (i\<^sub>\<epsilon> (f (e\<^sub>\<epsilon> x\<^sub>\<epsilon>)), f\<^sub>d x\<^sub>d) \<and> D\<^sub>s\<^sub>p \<epsilon> d x))\<close>




paragraph \<open>Convention\<close>

\<phi>reasoner_group separatable_unzip__all = (1000, [1, 3000]) for \<open>separatable_unzip z uz D\<^sub>u m m\<^sub>1 m\<^sub>2 f g\<close>
      \<open>If and how could a pairwise separated mapping \<open>f \<oplus>\<^sub>f g\<close> that is applied on an unzipped structure
       \<open>F(T\<^emph>U)\<close> over some pair data \<open>T\<^emph>U\<close>, be represneted as element-wise mapping over the original structure.\<close>
  and separatable_unzip = (1000, [1000,1030]) in separatable_unzip__all \<open>default group\<close>

  and separatable_zip__all = (1000, [1,3000]) for \<open>separatable_zip uz z D\<^sub>z m m\<^sub>1 m\<^sub>2 f g\<close>
      \<open>If and how could an element-wise mapping \<open>m (f \<oplus>\<^sub>f g)\<close> of pairwisely separated element mapping \<open>f \<oplus>\<^sub>f g\<close>
       that is applied on the zip of two structure \<open>F(T)\<close> and \<open>F(U)\<close>, be separated to two mappings
       \<open>m\<^sub>1\<close> and \<open>m\<^sub>2\<close> over \<open>F(T)\<close> and \<open>F(U)\<close> respectively\<close>
  and separatable_zip = (1000, [1000,1030]) in separatable_zip__all \<open>default group\<close>
  and separatable_zip__norm = (2000, [2000,2100]) in separatable_zip__all
      \<open>normalization\<close>

  and compositional_mapper__all = (1000, [1, 3000]) for \<open>compositional_mapper m\<^sub>1 m\<^sub>2 m\<^sub>3 D f g\<close> \<open>\<close>
  and compositional_mapper = (1000, [1000,1030]) in compositional_mapper__all \<open>\<close>

  and domain_of_inner_map__all = (1000, [1, 3000]) for \<open>domain_of_inner_map mapper D\<^sub>i\<close> \<open>\<close>
  and domain_of_inner_map = (1000, [1000,1030]) in domain_of_inner_map__all \<open>\<close>

  and separatable_module_zip__all = (1000, [1, 3000])
      for (\<open>separatable_module_zip flag d a b c uz' z' uz z D f g f' g'\<close>)
      \<open>separatable zip and unzip operations of a module \<phi>-type\<close>
  and separatable_module_zip = (1000, [1000,1030]) in separatable_module_zip__all
      \<open>the default group\<close>

  and module_mapper__all = (1000, [1, 3000])
      for (\<open>module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C C\<^sub>c C\<^sub>d c \<epsilon> d\<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g\<close>,
           \<open>module_mapper\<^sub>3\<^sub>\<epsilon> c \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g\<close>,
           \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R c \<epsilon> sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f' g\<close>,
           \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f' g\<close>,
           \<open>module_mapper\<^sub>1\<^sub>3\<^sub>C C\<^sub>c C\<^sub>d d a da c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f\<^sub>c f g\<close>,
           \<open>module_mapper\<^sub>1\<^sub>2\<^sub>L d a sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f\<close>,
           \<open>module_mapper\<^sub>3\<^sub>1\<^sub>C C\<^sub>c C\<^sub>d c b db d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g\<close>,
           \<open>module_mapper\<^sub>2\<^sub>1\<^sub>L b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f'\<close>)
      \<open>transformation mappers of module \<phi>-types\<close>
  and module_mapper = (1000, [1000, 1030]) in module_mapper__all
      \<open>the default group\<close>
  and module_mapper_default = (10,[10,30]) in module_mapper__all
      \<open>default rules\<close>
  and module_mapper_syserr = (0,[0,0]) < module_mapper__all
      \<open>sys error\<close>

declare [[
  \<phi>reason_default_pattern
      \<open>domain_by_mapper ?D' ?m ?D ?var_f _\<close> \<Rightarrow> \<open>domain_by_mapper ?D' ?m ?D _ _\<close> (100)
  and \<open>separatable_unzip ?z ?uz _ ?m _ _ ?var_f ?var_g\<close> \<Rightarrow>
      \<open>separatable_unzip ?z ?uz _ ?m _ _ _ _\<close>                       (100)
  and \<open>separatable_cond_unzip ?C ?z ?uz _ ?m _ _ ?var_f ?var_g\<close> \<Rightarrow>
      \<open>separatable_cond_unzip ?C ?z ?uz _ ?m _ _ _ _\<close>               (100)
  and \<open>separatable_zip ?uz ?z _ ?m _ _ ?var_f ?var_g\<close> \<Rightarrow>
      \<open>separatable_zip ?uz ?z _ ?m _ _ _ _\<close>                         (100)
  and \<open>separatable_cond_zip ?C ?uz ?z _ ?m _ _ ?var_f ?var_g\<close> \<Rightarrow>
      \<open>separatable_cond_zip ?C ?uz ?z _ ?m _ _ _ _\<close>                  (100)
  and \<open>compositional_mapper ?m\<^sub>1 ?m\<^sub>2 _ _ ?var_f ?var_g\<close> \<Rightarrow>
      \<open>compositional_mapper ?m\<^sub>1 _ _ _ _ _\<close>
      \<open>compositional_mapper _ ?m\<^sub>2 _ _ _ _\<close>                           (100)
  and \<open>domain_of_inner_map ?m _\<close> \<Rightarrow> \<open>domain_of_inner_map ?m _\<close>                                  (100)
  and \<open>separatable_module_zip ?flag ?var_d ?var_a ?var_b ?var_c ?uz' ?z' ?uz ?z _ _ _ _ _\<close> \<Rightarrow>
      \<open>separatable_module_zip ?flag _ _ _ _  ?uz' ?z' ?uz ?z _ _ _ _ _\<close>                      (100)

  and \<open>module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C ?C\<^sub>c ?C\<^sub>d ?c ?\<epsilon> ?d\<epsilon> ?d ?sp ?jn ?e\<^sub>\<epsilon> ?i\<^sub>\<epsilon> ?D\<^sub>\<epsilon>\<^sub>E ?D\<^sub>\<epsilon>\<^sub>I ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C ?C\<^sub>c ?C\<^sub>d ?c ?\<epsilon> ?d\<epsilon> ?d ?sp ?jn ?e\<^sub>\<epsilon> ?i\<^sub>\<epsilon> ?D\<^sub>\<epsilon>\<^sub>E ?D\<^sub>\<epsilon>\<^sub>I ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close>    (100)
  and \<open>module_mapper\<^sub>3\<^sub>\<epsilon> ?c ?\<epsilon> ?d ?sp ?jn ?e\<^sub>\<epsilon> ?i\<^sub>\<epsilon> ?D\<^sub>\<epsilon>\<^sub>E ?D\<^sub>\<epsilon>\<^sub>I ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>3\<^sub>\<epsilon> ?c ?\<epsilon> ?d ?sp ?jn ?e\<^sub>\<epsilon> ?i\<^sub>\<epsilon> ?D\<^sub>\<epsilon>\<^sub>E ?D\<^sub>\<epsilon>\<^sub>I ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close>              (100)
  and \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R ?c ?\<epsilon> ?sp ?jn ?e\<^sub>\<epsilon> ?i\<^sub>\<epsilon> ?D\<^sub>\<epsilon>\<^sub>E ?D\<^sub>\<epsilon>\<^sub>I ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R ?c ?\<epsilon> ?sp ?jn ?e\<^sub>\<epsilon> ?i\<^sub>\<epsilon> ?D\<^sub>\<epsilon>\<^sub>E ?D\<^sub>\<epsilon>\<^sub>I ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _\<close>                   (100)
  and \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L ?\<epsilon> ?d ?sp ?jn ?e\<^sub>\<epsilon> ?i\<^sub>\<epsilon> ?D\<^sub>\<epsilon>\<^sub>E ?D\<^sub>\<epsilon>\<^sub>I ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L ?\<epsilon> ?d ?sp ?jn ?e\<^sub>\<epsilon> ?i\<^sub>\<epsilon> ?D\<^sub>\<epsilon>\<^sub>E ?D\<^sub>\<epsilon>\<^sub>I ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _\<close>                   (100)

  and \<open>module_mapper\<^sub>1\<^sub>3\<^sub>C ?C\<^sub>c ?C\<^sub>d ?d ?a ?da ?c ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>1\<^sub>3\<^sub>C ?C\<^sub>c ?C\<^sub>d ?d ?a ?da ?c ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close>                   (100)
  and \<open>module_mapper\<^sub>1\<^sub>3 ?d ?a ?c ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>1\<^sub>3 ?d ?a ?c ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close>                               (100)
  and \<open>module_mapper\<^sub>1\<^sub>2\<^sub>L ?d ?a ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>1\<^sub>2\<^sub>L ?d ?a ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _\<close>                                      (100)
  and \<open>module_mapper\<^sub>1\<^sub>2\<^sub>R ?a ?c ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>1\<^sub>2\<^sub>R ?a ?c ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _\<close>                                      (100)

  and \<open>module_mapper\<^sub>3\<^sub>1\<^sub>C ?C\<^sub>c ?C\<^sub>d ?c ?b ?db ?d ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>3\<^sub>1\<^sub>C ?C\<^sub>c ?C\<^sub>d ?c ?b ?db ?d ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close>                    (100)
  and \<open>module_mapper\<^sub>3\<^sub>1 ?c ?b ?d ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>3\<^sub>1 ?c ?b ?d ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _ _ _\<close>                                (100)
  and \<open>module_mapper\<^sub>2\<^sub>1\<^sub>R ?c ?b ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>2\<^sub>1\<^sub>R ?c ?b ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _\<close>                                      (100)
  and \<open>module_mapper\<^sub>2\<^sub>1\<^sub>L ?b ?d ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _\<close> \<Rightarrow>
      \<open>module_mapper\<^sub>2\<^sub>1\<^sub>L ?b ?d ?sp ?jn ?D\<^sub>s\<^sub>p ?D\<^sub>j\<^sub>n _ _ _ _\<close>                                      (100)


  and \<open>domain_by_mapper ?D' ?m ?D ?f ?D\<^sub>d\<^sub>m\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (domain_by_mapper ?D' ?m ?D ?f ?D\<^sub>d\<^sub>m))\<close>            (0)
  and \<open>separatable_unzip ?z ?uz ?D\<^sub>u ?m ?m\<^sub>1 ?m\<^sub>2 ?f ?g\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (separatable_unzip ?z ?uz ?D\<^sub>u ?m ?m\<^sub>1 ?m\<^sub>2 ?f ?g))\<close> (0)
  and \<open>separatable_zip ?uz ?z ?D\<^sub>z ?m ?m\<^sub>1 ?m\<^sub>2 ?f ?g\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (separatable_zip ?uz ?z ?D\<^sub>z ?m ?m\<^sub>1 ?m\<^sub>2 ?f ?g))\<close>  (0)
  and \<open>separatable_cond_unzip ?C ?z ?uz ?D\<^sub>u ?m ?m\<^sub>1 ?m\<^sub>2 ?f ?g\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (separatable_cond_unzip ?C ?z ?uz ?D\<^sub>u ?m ?m\<^sub>1 ?m\<^sub>2 ?f ?g))\<close> (0)
  and \<open>separatable_cond_zip ?C ?uz ?z ?D\<^sub>z ?m ?m\<^sub>1 ?m\<^sub>2 ?f ?g\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (separatable_cond_zip ?C ?uz ?z ?D\<^sub>z ?m ?m\<^sub>1 ?m\<^sub>2 ?f ?g))\<close>  (0)
  and \<open>compositional_mapper ?m\<^sub>1 ?m\<^sub>2 ?m\<^sub>3 ?D ?f ?g\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (compositional_mapper ?m\<^sub>1 ?m\<^sub>2 ?m\<^sub>3 ?D ?f ?g))\<close>    (0)
  and \<open>domain_of_inner_map ?m ?D\<^sub>i\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (domain_of_inner_map ?m ?D\<^sub>i))\<close>                   (0)
  and \<open>separatable_module_zip ?flag ?d ?a ?b ?c ?uz' ?z' ?uz ?z ?D ?f ?g ?f' ?g'\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed Rule\<close> (separatable_module_zip ?flag ?d ?a ?b ?c ?uz' ?z' ?uz ?z ?D ?f ?g ?f' ?g'))\<close>  (0)
,
  \<phi>default_reasoner_group
      \<open>separatable_unzip _ _ _ _ _ _ _ _\<close> : %separatable_unzip  (100)
  and \<open>separatable_zip _ _ _ _ _ _ _ _\<close>   : %separatable_zip    (100)
  and \<open>separatable_cond_unzip _ _ _ _ _ _ _ _ _\<close> : %separatable_unzip  (100)
  and \<open>separatable_cond_zip _ _ _ _ _ _ _ _ _\<close>   : %separatable_zip    (100)
  and \<open>compositional_mapper _ _ _ _ _ _\<close>: %compositional_mapper (100)
  and \<open>domain_of_inner_map _ _\<close>         : %domain_of_inner_map  (100)
  and \<open>separatable_module_zip _ _ _ _ _  _ _ _ _ _ _ _ _ _\<close>  : %separatable_module_zip (100)
  and \<open>module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close> : %module_mapper (100)
  and \<open>module_mapper\<^sub>3\<^sub>\<epsilon> _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>        : %module_mapper (100)
  and \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>           : %module_mapper (100)
  and \<open>module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>           : %module_mapper (100)
]]

paragraph \<open>Basic Rules\<close>

subparagraph \<open>Module Error\<close>

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>, joiner\<close> jn
               \<open>, identity constructor\<close> i\<^sub>\<epsilon> \<open>and destructor\<close> e\<^sub>\<epsilon> \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>3\<^sub>\<epsilon> c \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g) \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>3\<^sub>\<epsilon> c \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>, joiner\<close> jn
               \<open>, identity constructor\<close> i\<^sub>\<epsilon> \<open>and destructor\<close> e\<^sub>\<epsilon> \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R c \<epsilon> sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f' g) \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R c \<epsilon> sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f' g \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>, joiner\<close> jn
               \<open>, identity constructor\<close> i\<^sub>\<epsilon> \<open>and destructor\<close> e\<^sub>\<epsilon> \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f' g) \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f' g \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>joiner\<close> jn
               \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>1\<^sub>3 d a c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f\<^sub>c f g) \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>1\<^sub>3 d a c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f\<^sub>c f g \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>joiner\<close> jn
               \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>1\<^sub>2\<^sub>L d a sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f) \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>1\<^sub>2\<^sub>L d a sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>joiner\<close> jn
               \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>1\<^sub>2\<^sub>R a c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>a f\<^sub>c f) \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>1\<^sub>2\<^sub>R a c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>a f\<^sub>c f \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>joiner\<close> jn
               \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>3\<^sub>1 c b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g) \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>3\<^sub>1 c b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>joiner\<close> jn
               \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>2\<^sub>1\<^sub>L b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f') \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>2\<^sub>1\<^sub>L b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f' \<close>
  unfolding ERROR_def
  by blast

lemma [\<phi>reason default %module_mapper_syserr]:
  \<open> ERROR TEXT(\<open>Fail to apply transformation mapper the module of spliter\<close> sp \<open>joiner\<close> jn
               \<open>, you may provide a LPR reasoning rule\<close>
               (module_mapper\<^sub>2\<^sub>1\<^sub>R c b sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f') \<open>to address the issue.\<close>)
\<Longrightarrow> module_mapper\<^sub>2\<^sub>1\<^sub>R c b sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f' \<close>
  unfolding ERROR_def
  by blast


subparagraph \<open>Module Conversions\<close>

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>3\<^sub>\<epsilon> c \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g
\<Longrightarrow> module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C True True c \<epsilon> d\<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g \<close>
  unfolding module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C_def module_mapper\<^sub>3\<^sub>\<epsilon>_def
  by simp

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R c \<epsilon> sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f' g
\<Longrightarrow> module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C True False c \<epsilon> d\<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' (\<lambda>x. case g x of (c,\<epsilon>) \<Rightarrow> (c,\<epsilon>,unspec)) \<close>
  unfolding module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C_def module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R_def
  by clarsimp fastforce

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L \<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f' g
\<Longrightarrow> module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C False True c \<epsilon> d\<epsilon> d sp jn e\<^sub>\<epsilon> i\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' (\<lambda>x. case g x of (\<epsilon>,d) \<Rightarrow> (unspec,\<epsilon>,d)) \<close>
  unfolding module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C_def module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L_def
  by clarsimp

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>1\<^sub>3 d a c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f\<^sub>c f g
\<Longrightarrow> module_mapper\<^sub>1\<^sub>3\<^sub>C True True d a da c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f\<^sub>c f g \<close>
  unfolding module_mapper\<^sub>1\<^sub>3\<^sub>C_def module_mapper\<^sub>1\<^sub>3_def
  by clarsimp

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>1\<^sub>2\<^sub>L d a sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>d f\<^sub>a f
\<Longrightarrow> module_mapper\<^sub>1\<^sub>3\<^sub>C False True d a da c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n
                    (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c). D (x\<^sub>a,x\<^sub>d)) f\<^sub>d f\<^sub>a (\<lambda>_. unspec) f (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c). jn a d (x\<^sub>a,x\<^sub>d)) \<close>
  unfolding module_mapper\<^sub>1\<^sub>3\<^sub>C_def module_mapper\<^sub>1\<^sub>2\<^sub>L_def
  by clarsimp

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>1\<^sub>2\<^sub>R a c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>a f\<^sub>c f
\<Longrightarrow> module_mapper\<^sub>1\<^sub>3\<^sub>C True False d a da c sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n
                    (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c). D (x\<^sub>a,x\<^sub>c)) (\<lambda>_. unspec) f\<^sub>a f\<^sub>c f (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c). jn c a (x\<^sub>c,x\<^sub>a)) \<close>
  unfolding module_mapper\<^sub>1\<^sub>3\<^sub>C_def module_mapper\<^sub>1\<^sub>2\<^sub>R_def
  by clarsimp

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>3\<^sub>1 c b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g
\<Longrightarrow> module_mapper\<^sub>3\<^sub>1\<^sub>C True True c b db d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f' g \<close>
  unfolding module_mapper\<^sub>3\<^sub>1_def module_mapper\<^sub>3\<^sub>1\<^sub>C_def
  by clarsimp

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>2\<^sub>1\<^sub>L b d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f f\<^sub>d f'
\<Longrightarrow> module_mapper\<^sub>3\<^sub>1\<^sub>C False True c b db d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f'
                    (\<lambda>x. case sp b d x of (x\<^sub>b,x\<^sub>d) \<Rightarrow> (unspec, x\<^sub>b, x\<^sub>d)) \<close>
  unfolding module_mapper\<^sub>2\<^sub>1\<^sub>L_def module_mapper\<^sub>3\<^sub>1\<^sub>C_def
  by clarsimp fastforce

lemma [\<phi>reason default %module_mapper_default]:
  \<open> module_mapper\<^sub>2\<^sub>1\<^sub>R c b sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f'
\<Longrightarrow> module_mapper\<^sub>3\<^sub>1\<^sub>C True False c b db d sp jn D\<^sub>s\<^sub>p D\<^sub>j\<^sub>n D f\<^sub>c f f\<^sub>d f'
                    (\<lambda>x. case sp c b x of (x\<^sub>c,x\<^sub>a) \<Rightarrow> (x\<^sub>c, x\<^sub>a, unspec))\<close>
  unfolding module_mapper\<^sub>3\<^sub>1\<^sub>C_def module_mapper\<^sub>2\<^sub>1\<^sub>R_def
  by clarsimp fastforce



paragraph \<open>Instances\<close>

subparagraph \<open>Identity Mappers\<close>

lemma [\<phi>reason add]:
  \<open> separatable_unzip (\<lambda>x. x) (\<lambda>x. x) UNIV (\<lambda>f. f) (\<lambda>f. f) (\<lambda>f. f) g r \<close>
  unfolding separatable_unzip_def
  by simp

lemma [\<phi>reason add]:
  \<open> separatable_zip (\<lambda>x. x) (\<lambda>x. x) UNIV (\<lambda>f. f) (\<lambda>f. f) (\<lambda>f. f) f g \<close>
  unfolding separatable_zip_def
  by simp

lemma [\<phi>reason add]:
  \<open> compositional_mapper (\<lambda>f. f) (\<lambda>f. f) (\<lambda>f. f) UNIV f g \<close>
  unfolding compositional_mapper_def
  by simp

lemma [\<phi>reason add]:
  \<open> domain_of_inner_map (\<lambda>f. f) (\<lambda>x. {x}) \<close>
  unfolding domain_of_inner_map_def
  by simp

lemma [\<phi>reason add]:
  \<open>domain_by_mapper (\<lambda>x. {x}) (\<lambda>f. f) (\<lambda>x. {x}) f UNIV\<close>
  unfolding domain_by_mapper_def
  by clarsimp

subparagraph \<open>Conditioned\<close>

lemma [\<phi>reason %separatable_zip__norm]:
  \<open> separatable_cond_unzip (LPR_ctrl C) (?\<^sub>Z (LPR_ctrl C) z m\<^sub>Z) (?\<^sub>U\<^sub>Z (LPR_ctrl C) uz m\<^sub>U) D\<^sub>U' m m\<^sub>f m\<^sub>g f g
\<Longrightarrow> separatable_cond_unzip C (?\<^sub>Z (LPR_ctrl C) z m\<^sub>Z) (?\<^sub>U\<^sub>Z (LPR_ctrl C) uz m\<^sub>U) D\<^sub>U' m m\<^sub>f m\<^sub>g f g \<close>
  unfolding LPR_ctrl_def .

lemma [\<phi>reason %separatable_zip__norm]:
  \<open> separatable_cond_zip (LPR_ctrl C) (?\<^sub>U\<^sub>Z (LPR_ctrl C) uz m\<^sub>U) (?\<^sub>Z (LPR_ctrl C) z m\<^sub>Z) D\<^sub>U' m m\<^sub>f m\<^sub>g f g
\<Longrightarrow> separatable_cond_zip C (?\<^sub>U\<^sub>Z (LPR_ctrl C) uz m\<^sub>U) (?\<^sub>Z (LPR_ctrl C) z m\<^sub>Z) D\<^sub>U' m m\<^sub>f m\<^sub>g f g \<close>
  unfolding LPR_ctrl_def .

lemma [\<phi>reason add]:
  \<open> \<g>\<u>\<a>\<r>\<d> separatable_unzip z uz D\<^sub>U m m\<^sub>f m\<^sub>g f g \<and>\<^sub>\<r>
          compositional_mapper m\<^sub>f m\<^sub>U m\<^sub>2 D\<^sub>m f fst \<and>\<^sub>\<r>
          compositional_mapper m\<^sub>Z m\<^sub>2 m D\<^sub>m\<^sub>2 (\<lambda>x. (x, unspec)) (f o fst)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] D\<^sub>U' : {x. if C then x \<in> D\<^sub>U else x \<in> D\<^sub>m \<inter> D\<^sub>m\<^sub>2}
\<Longrightarrow> separatable_cond_unzip C (?\<^sub>Z C z m\<^sub>Z) (?\<^sub>U\<^sub>Z C uz m\<^sub>U) D\<^sub>U' m m\<^sub>f (?\<^sub>M C m\<^sub>g) f g \<close>
  unfolding \<r>Guard_def compositional_mapper_def Ant_Seq_def
            separatable_unzip_def separatable_cond_unzip_def Simplify_def
  by (cases C; clarsimp; metis prod.map_beta)

lemma [\<phi>reason add]:
  \<open> \<g>\<u>\<a>\<r>\<d> separatable_zip uz z D\<^sub>U m m\<^sub>f m\<^sub>g f g \<and>\<^sub>\<r>
          compositional_mapper m m\<^sub>Z m\<^sub>2 D\<^sub>m (f \<otimes>\<^sub>f (\<lambda>_. unspec)) (\<lambda>x. (x, unspec)) \<and>\<^sub>\<r>
          compositional_mapper m\<^sub>U m\<^sub>2 m\<^sub>f D\<^sub>m\<^sub>2 fst (\<lambda>x. (f x, unspec))
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] D\<^sub>U' : {x. if C then x \<in> D\<^sub>U else fst x \<in> D\<^sub>m \<inter> D\<^sub>m\<^sub>2}
\<Longrightarrow> separatable_cond_zip C (?\<^sub>U\<^sub>Z C uz m\<^sub>U) (?\<^sub>Z C z m\<^sub>Z) D\<^sub>U' m m\<^sub>f (?\<^sub>M C m\<^sub>g) f g \<close>
  unfolding \<r>Guard_def compositional_mapper_def Ant_Seq_def
            separatable_zip_def separatable_cond_zip_def Simplify_def
  by (cases C; clarsimp)


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
      reported to users for each transformation application.
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

(*It seems we have the need to give bifunctor*)

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

subsubsection \<open>Transformation Bi-Functor\<close>

definition \<open>Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper \<longleftrightarrow>
  (\<forall>x g\<^sub>1 g\<^sub>2. (\<forall>a \<in> D\<^sub>1 x. a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b) \<longrightarrow>
            (\<forall>a \<in> D\<^sub>2 x. a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b) \<longrightarrow>
            (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x) \<longrightarrow>
            (x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y))\<close>

definition \<open>Functional_Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 pred_mapper func_mapper \<longleftrightarrow>
    (\<forall>x f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2. (\<forall>a \<in> D\<^sub>1 x. a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f\<^sub>1 a \<Ztypecolon> U\<^sub>1 \<w>\<i>\<t>\<h> P\<^sub>1 a)
                \<longrightarrow> (\<forall>a \<in> D\<^sub>2 x. a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f\<^sub>2 a \<Ztypecolon> U\<^sub>2 \<w>\<i>\<t>\<h> P\<^sub>2 a)
                \<longrightarrow> (\<forall>a. a \<in> D\<^sub>1 x \<longrightarrow> f\<^sub>1 a \<in> R\<^sub>1 x) \<and> (\<forall>a. a \<in> D\<^sub>2 x \<longrightarrow> f\<^sub>2 a \<in> R\<^sub>2 x)
                \<longrightarrow> (x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<w>\<i>\<t>\<h> pred_mapper f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x))\<close>

lemma infer_biFTF_from_biFT:
  \<open> Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper
\<Longrightarrow> Object_Equiv (Fb U\<^sub>1 U\<^sub>2) eq
\<Longrightarrow> (\<forall>f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x y. mapper (\<lambda>a b. b = f\<^sub>1 a \<and> P\<^sub>1 a) (\<lambda>a b. b = f\<^sub>2 a \<and> P\<^sub>2 a) x y
                  \<longrightarrow> eq y (fm f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x) \<and> pm f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x)
\<Longrightarrow> Functional_Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 pm fm \<close>
  unfolding Functional_Transformation_BiFunctor_def Transformation_BiFunctor_def
            Object_Equiv_def
  apply clarify
  subgoal premises prems for x f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2
    by (insert prems(1)[THEN spec[where x=x],
                        THEN spec[where x=\<open>\<lambda>a b. b = f\<^sub>1 a \<and> P\<^sub>1 a\<close>],
                        THEN spec[where x=\<open>\<lambda>a b. b = f\<^sub>2 a \<and> P\<^sub>2 a\<close>]]
               prems(2-),
        clarsimp simp add: Transformation_def,
        blast) .

subsubsection \<open>Transformation Functor with Parameterization\<close>

definition \<open>Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R mapper \<longleftrightarrow>
  (\<forall>x g. (\<forall>p. \<forall>a \<in> D p x. a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b) \<longrightarrow>
             (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x) \<longrightarrow>
             (x \<Ztypecolon> F1 T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U \<s>\<u>\<b>\<j> y. mapper g x y))\<close>

definition \<open>Functional_Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R pred_mapper func_mapper \<longleftrightarrow>
            (\<forall>x f P. (\<forall>p. \<forall>a \<in> D p x. a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f p a \<Ztypecolon> U p \<w>\<i>\<t>\<h> P p a)
                \<longrightarrow> (\<forall>p a. a \<in> D p x \<longrightarrow> f p a \<in> R p x)
                \<longrightarrow> (x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper f P x))\<close>

lemma infer_FTF\<^sub>\<Lambda>_from_FT\<^sub>\<Lambda>:
  \<open> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R mapper
\<Longrightarrow> Abstract_Domain (F1 T) P\<^sub>T
\<Longrightarrow> Abstract_Domain (F2 U) P\<^sub>U
\<Longrightarrow> Object_Equiv (F2 U) eq
\<Longrightarrow> (\<forall>f P x y. P\<^sub>T x \<and> P\<^sub>U y \<and> mapper (\<lambda>p a b. b = f p a \<and> P p a) x y \<longrightarrow> eq y (fm f P x) \<and> pm f P x)
\<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R pm fm \<close>
  unfolding Functional_Transformation_Functor\<^sub>\<Lambda>_def Transformation_Functor\<^sub>\<Lambda>_def
            Object_Equiv_def Abstract_Domain_def Action_Tag_def Inhabited_def \<r>EIF_def
  apply clarsimp
  subgoal premises prems for x f P
    by (insert prems(1)[THEN spec[where x=x], THEN spec[where x=\<open>\<lambda>p a b. b = f p a \<and> P p a\<close>]]
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


paragraph \<open>With Parameter\<close>

definition \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I Ft Fu F3 T U D z \<longleftrightarrow>
              (\<forall>x y. (x,y) \<in> D \<longrightarrow> ((x,y) \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z (x,y) \<Ztypecolon> F3 (\<lambda>p. T p \<^emph> U p)))\<close>

definition \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E Ft Fu F3 T U un \<longleftrightarrow>
              (\<forall>z. z \<Ztypecolon> F3 (\<lambda>p. T p \<^emph> U p) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un z \<Ztypecolon> Ft T \<^emph> Fu U)\<close>

definition \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond Ft Fu F3 C\<^sub>W T U D z \<longleftrightarrow>
              (\<forall>x y. (x,y) \<in> D \<longrightarrow> ((x,y) \<Ztypecolon> Ft(T) \<^emph>[C\<^sub>W] Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z (x,y) \<Ztypecolon> F3 (\<lambda>p. T p \<^emph>[C\<^sub>W] U p)))\<close>

definition \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond Ft Fu F3 C\<^sub>R T U D un \<longleftrightarrow>
              (\<forall>z. z \<in> D \<longrightarrow> (z \<Ztypecolon> F3 (\<lambda>p. T p \<^emph>[C\<^sub>R] U p) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un z \<Ztypecolon> Ft T \<^emph>[C\<^sub>R] Fu U))\<close>


subsubsection \<open>Semimodule\<close>

text \<open>Convention: the domain \<open>Dx\<close> of object gives proof obligation but the domain \<open>Ds\<close> of scalar is
  a reasoning guard. Recall the reasoning is guided by types, the reasoning should be determined
  only by types, where a proof obligation about the objects are yielded as an outcome.
  \<open>Dx\<close> is totally about objects but \<open>Ds\<close> is about scalar and scalar is in type-level.
\<close>

definition Semimodule_Zero :: \<open>('s \<Rightarrow> ('c::one,'a) \<phi>) \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>Semimodule_Zero F zero \<longleftrightarrow> (\<forall>x. (x \<Ztypecolon> F zero) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1)\<close>

definition Closed_Semimodule_Zero :: \<open>('s \<Rightarrow> ('c::one,'a) \<phi>) \<Rightarrow> 's \<Rightarrow> bool\<close>
  where \<open>Closed_Semimodule_Zero F zero \<longleftrightarrow> (\<forall>x. (x \<Ztypecolon> F zero) = 1)\<close>
  \<comment> \<open>It is actually a very strong property particularly when \<open>T\<close> is an empty \<phi>-type of empty
      abstract domain. It excludes functional homomorphism like \<open>F c T \<equiv> \<psi> c \<Zcomp>\<^sub>f T\<close>.\<close>

definition Semimodule_One\<^sub>I :: \<open>('s \<Rightarrow> ('c,'a) \<phi>)
                            \<Rightarrow> ('c,'a\<^sub>1) \<phi>
                            \<Rightarrow> 's \<Rightarrow> ('a\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('a\<^sub>1 \<Rightarrow> 'a) \<Rightarrow> ('a\<^sub>1 \<Rightarrow> bool)
                            \<Rightarrow> bool\<close>
  where \<open>Semimodule_One\<^sub>I F T\<^sub>1 one D f P \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F one \<w>\<i>\<t>\<h> P x))\<close>
  \<comment> \<open>Domain information should be given in types. The unit scalar \<open>one\<close> belongs to domain info.
      So, the value of \<open>one\<close> should be able to be determined solely from \<open>T\<^sub>1\<close> and \<open>F\<close>, but no \<open>x\<close>.\<close>

definition Semimodule_One\<^sub>E :: \<open>('s \<Rightarrow> ('c,'a) \<phi>)
                            \<Rightarrow> ('c,'a\<^sub>1) \<phi>
                            \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a\<^sub>1) \<Rightarrow> ('a \<Rightarrow> bool)
                            \<Rightarrow> bool\<close>
  where \<open>Semimodule_One\<^sub>E F T\<^sub>1 one D f P \<longleftrightarrow> (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> F one \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T\<^sub>1 \<w>\<i>\<t>\<h> P x))\<close>

(* no need, as covered by the rule of \<open>individual \<rightarrow> segment\<close>
definition Semimodule_Cons :: \<open> ('s \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c::sep_magma,'a) \<phi>) \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c,'a\<^sub>1) \<phi>
                             \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'a\<^sub>1 \<Rightarrow> 'a \<Rightarrow> bool)
                             \<Rightarrow> ('a\<^sub>1 \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('a\<^sub>1 \<Rightarrow> 'a \<Rightarrow> 'a)
                             \<Rightarrow> bool\<close>
  where \<open>Semimodule_Cons F T T\<^sub>1 D\<^sub>s D incr cons \<longleftrightarrow>
            (\<forall>s a x. D\<^sub>s s \<and> D s a x \<longrightarrow> ( (a,x) \<Ztypecolon> T\<^sub>1 \<^emph> F s T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> cons a x \<Ztypecolon> F (incr a s) T ))\<close>
  \<comment> \<open>Given a \<phi>-type \<open>T\<^sub>1 \<noteq> F s' T'\<close> not in a semimodule form, how to merge it into an existing semimodule.
      \<open>Semimodule_Zero\<close> and \<open>Semimodule_Cons\<close> derives \<open>Semimodule_Cons\<close>\<close>
*)

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
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 's\<^sub>c)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t)
                                     \<Rightarrow> bool\<close>
  where \<open>Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
      \<longleftrightarrow> (\<forall>s t x. Ds s \<and> Dt t \<and> Dx s t x \<longrightarrow> (x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fs s (Ft t T)))\<close>

text \<open>The extended scalar association operator for Finite Multiplicative Quantification is just uncurrying.\<close>

definition Semimodule_Scalar_Assoc\<^sub>\<Lambda>\<^sub>I :: \<open> ('s\<^sub>s \<Rightarrow> ('p\<^sub>s \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi>) \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>_\<^sub>t) \<phi>)
                                     \<Rightarrow> ('s\<^sub>t \<Rightarrow> ('p\<^sub>t \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi>)
                                     \<Rightarrow> ('s\<^sub>c \<Rightarrow> ('p\<^sub>s \<times> 'p\<^sub>t \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>t) \<phi>)
                                     \<Rightarrow> ('p\<^sub>s \<Rightarrow> 'p\<^sub>t \<Rightarrow> ('c,'a) \<phi>)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 's\<^sub>c)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t)
                                     \<Rightarrow> bool\<close>
  where \<open>Semimodule_Scalar_Assoc\<^sub>\<Lambda>\<^sub>I Fs Ft Fc T Ds Dt Dx smul f
      \<longleftrightarrow> (\<forall>s t x. Ds s \<and> Dt t \<and> Dx s t x \<longrightarrow> (x \<Ztypecolon> Fs s (\<lambda>p\<^sub>s. Ft t (T p\<^sub>s)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fc (smul s t) (case_prod T)))\<close>

definition Semimodule_Scalar_Assoc\<^sub>\<Lambda>\<^sub>E :: \<open> ('s\<^sub>s \<Rightarrow> ('p\<^sub>s \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi>) \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>_\<^sub>t) \<phi>)
                                     \<Rightarrow> ('s\<^sub>t \<Rightarrow> ('p\<^sub>t \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi>)
                                     \<Rightarrow> ('s\<^sub>c \<Rightarrow> ('p\<^sub>s \<times> 'p\<^sub>t \<Rightarrow> ('c,'a) \<phi>) \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>t) \<phi>)
                                     \<Rightarrow> ('p\<^sub>s \<times> 'p\<^sub>t \<Rightarrow> ('c,'a) \<phi>)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> bool)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 's\<^sub>c)
                                     \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t)
                                     \<Rightarrow> bool\<close>
  where \<open>Semimodule_Scalar_Assoc\<^sub>\<Lambda>\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
      \<longleftrightarrow> (\<forall>s t x. Ds s \<and> Dt t \<and> Dx s t x \<longrightarrow> (f s t x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fs s (\<lambda>p\<^sub>s. Ft t (\<lambda>p\<^sub>t. T (p\<^sub>s, p\<^sub>t)))))\<close>


definition Semimodule_SDistr_Homo\<^sub>Z :: \<open> ('s \<Rightarrow> ('c::sep_magma,'a) \<phi>)
                                    \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                    \<Rightarrow> bool\<close>
  where \<open>Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x \<longrightarrow> (x \<Ztypecolon> F t \<^emph> F s \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (s + t) ))\<close>
  \<comment> \<open>The left distributive law (i.e., the distributivity of scalar addition) of a left-module.
      Note the right distributive law (i.e., the distributivity of vector addition) is just the separation homomorphism.
      So, when both of \<open>Semimodule_Scalar_Assoc\<close>, \<open>Separation_Homo\<close>, \<open>Semimodule_SDistr_Homo\<^sub>Z\<close>, and
      homomorphism of identity element, are satisfied, it is then a semimodule.
\<close>

definition Semimodule_SDistr_Homo\<^sub>Z_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi>)
                                        \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                        \<Rightarrow> bool\<close>
  where \<open>Semimodule_SDistr_Homo\<^sub>Z_rev F Ds Dx' z' Dx z \<longleftrightarrow>
            (Semimodule_SDistr_Homo\<^sub>Z F Ds Dx' z' \<longrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> t ##\<^sub>+ s \<and> Dx t s x \<longrightarrow>
                  (x \<Ztypecolon> F t \<^emph> F s \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (t + s) )))\<close>
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


definition Semimodule_SDistr_Homo\<^sub>S :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi>)
                                    \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool)
                                    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                    \<Rightarrow> bool\<close>
  where \<open>Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz \<longleftrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x \<longrightarrow>
                (x \<Ztypecolon> F (s + t) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t \<^emph> F s ))\<close>

definition Semimodule_SDistr_Homo\<^sub>S_rev :: \<open>('s \<Rightarrow> ('c::sep_magma,'a) \<phi>)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                        \<Rightarrow> ('s::partial_add_magma \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool)
                                        \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                        \<Rightarrow> bool\<close>
  where \<open>Semimodule_SDistr_Homo\<^sub>S_rev F Dx' uz' Ds Dx uz \<longleftrightarrow>
            (Semimodule_SDistr_Homo\<^sub>S F Ds Dx' uz' \<longrightarrow>
            (\<forall>s t x. Ds s \<and> Ds t \<and> t ##\<^sub>+ s \<and> Dx t s x \<longrightarrow>
                (x \<Ztypecolon> F (t + s) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t \<^emph> F s )))\<close>
  \<comment>\<open>Also not a template parameter, see \<open>Semimodule_SDistr_Homo\<^sub>Z_rev\<close>\<close>

definition Semimodule_No_SDistr :: \<open>'a \<Rightarrow> bool\<close>
  where \<open>Semimodule_No_SDistr F \<equiv> True\<close>
  \<comment> \<open>tagging the \<phi>-type operator \<open>F\<close> has no scalar associativity, so hinting the use of the rules
      which are unsafe for scalar associativity.\<close>


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

paragraph \<open>Over Parameterized Types\<close>

definition Tyops_Commute\<^sub>\<Lambda>\<^sub>I :: \<open> (('c\<^sub>G,'a\<^sub>G) \<phi> \<Rightarrow> ('c,'a) \<phi>)
                             \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>F,'a\<^sub>F) \<phi>)
                             \<Rightarrow> (('p \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>) \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                             \<Rightarrow> (('p \<Rightarrow> ('c\<^sub>F,'a\<^sub>F) \<phi>) \<Rightarrow> ('c,'b) \<phi>)
                             \<Rightarrow> ('p \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>)
                             \<Rightarrow> ('a \<Rightarrow> bool)
                             \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)
                             \<Rightarrow> bool\<close>
  where \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>I F F' G G' T D r \<longleftrightarrow>
            (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (\<lambda>p. F' (T p)) \<s>\<u>\<b>\<j> y. r x y)) \<close>

definition Tyops_Commute\<^sub>\<Lambda>\<^sub>E :: \<open> (('p \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>) \<Rightarrow> ('c,'a) \<phi>)
                             \<Rightarrow> (('p \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>) \<Rightarrow> ('c\<^sub>F,'a\<^sub>F) \<phi>)
                             \<Rightarrow> (('c\<^sub>T,'a\<^sub>T) \<phi> \<Rightarrow> ('c\<^sub>G,'a\<^sub>G) \<phi>)
                             \<Rightarrow> (('c\<^sub>F,'a\<^sub>F) \<phi> \<Rightarrow> ('c,'b) \<phi>)
                             \<Rightarrow> ('p \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>)
                             \<Rightarrow> ('a \<Rightarrow> bool)
                             \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)
                             \<Rightarrow> bool\<close>
  where \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>E F F' G G' T D r \<longleftrightarrow>
            (\<forall>x. D x \<longrightarrow> (x \<Ztypecolon> F (\<lambda>p. G (T p)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r x y)) \<close>


subsection \<open>Conventions\<close>

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
 and \<phi>TA_property = (1000, [1000, 1030]) for \<open>_\<close> in \<phi>type_algebra_properties
    \<open>Cutting rules\<close>
 and \<phi>TA_derived_properties = (50, [50,50]) for \<open>_\<close> in \<phi>type_algebra_properties
    \<open>Automatically derived properties.\<close>
 and \<phi>TA_varify_out = (3900, [3900,3900]) for \<open>_\<close> in \<phi>type_algebra_all_properties and > \<phi>type_algebra_properties
    \<open>Systematic rules of \<phi>-type algebraic properties that varifies OUT arguments that are not varibales\<close>
 and \<phi>TA_commutativity = (100, [20, 3800]) for (\<open>Tyops_Commute F F' G G' T D r\<close>,
                                                 \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r\<close>,
                                                 \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r\<close>)
                                            in \<phi>type_algebra_properties
    \<open>commutativities\<close>
 and \<phi>TA_commutativity_default = (100, [100, 100]) in \<phi>TA_commutativity
    \<open>rules not assigned with a specific priority and group\<close>
 and \<phi>TA_derived_commutativity = (50,[50,50]) in \<phi>TA_commutativity and in \<phi>TA_derived_properties
    \<open>commutativities. Note, because Tyops_Commute is also a tempalte property which may trigger
     instantiation of a lot templates. The deriviation should be prudent, which may provide templates
     to allow users to manually instantiation but registering to the \<phi>-LPR only when the instantiated
     commutativity is certainly correct, because user overridings cannot override the rules
     instantiated by the derived commutativity to be overrided. \<close>

subsubsection \<open>Groups for Specific Properties\<close>

\<phi>reasoner_group Object_Sep_Homo_functor = (50, [50,50]) for (\<open>Object_Sep_Homo\<^sub>I T D\<close>, \<open>Object_Sep_Homo\<^sub>E T\<close>)
                                                         in \<phi>type_algebra_properties
    \<open>Object_Sep_Homo for functors\<close>

subsubsection \<open>Derived Rules\<close>

\<phi>reasoner_group deriving_local_rules = (200, [180,220]) for \<open>_\<close> > default
    \<open>Local reasoning rules such as those extracted from induction hypotheses used during deriving.\<close>

 and ToA_derived_one_to_one_functor = (70, [70,70]) for \<open>x \<Ztypecolon> F(T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> F(U)\<close> in ToA_derived
    \<open>Derived transformation in form \<open>x \<Ztypecolon> F(T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> F(U)\<close>, of a high priority as this is what
     should be attempted in reasoning.\<close>
 and To_ToA_derived_Tr_functor = (60, [60,60]) for \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r x y \<w>\<i>\<t>\<h> P @action to U\<close>
                                                in To_ToA_derived
    \<open>Derived To-Transformation rules for transformation functor\<close>
 and To_ToA_derived_Tr_functor_fuzzy = (55, [55,55]) for \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<s>\<u>\<b>\<j> y. r x y \<w>\<i>\<t>\<h> P @action to U\<close>
                                                in To_ToA_derived and < To_ToA_derived_Tr_functor
    \<open>when the annotated target \<phi>-type is in the element algebra but not the container\<close>
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
 and derived_SE_sdistr_comm_no_adz = (39, [39, 39]) in derived_SE_scalar_distr
    \<open>scalar distributivity on commutative semigroup and non-zero scalar\<close>
 and derived_SE_sdistr = (37, [37, 38]) in derived_SE_scalar_distr < derived_SE_sdistr_comm_no_adz
    \<open>Derived rules for scalar distributivity on commutative semigroup\<close>
 and derived_SE_sdistr_noassoc = (33, [33, 33]) in derived_SE_scalar_distr < derived_SE_sdistr
    \<open>Derived rules for scalar distributivity on separational magma\<close>
 and derived_SE_red_scalar_one = (30, [30,30]) for (\<open>x \<Ztypecolon> F one T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>, \<open>y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one T\<close>)
                                                in ToA_derived and < derived_SE_sdistr_noassoc
    \<open>reduce scalar one\<close>
 and derived_SE_inj_to_module = (27, [27,28]) for (\<open>x \<Ztypecolon> F one T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>, \<open>y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F one T\<close>)
                                               in ToA_derived and < derived_SE_red_scalar_one
    \<open>Derived rules lifting the target part into the module operator \<open>F\<close>\<close>
 and To_ToA_derived_SAssoc = (61, [61,61])
                             for (\<open>x \<Ztypecolon> F st T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F s (F t T) \<s>\<u>\<b>\<j> y. r y @action to (\<s>\<p>\<l>\<i>\<t>-\<a>\<s>\<s>\<o>\<c> s t)\<close>)
                             in To_ToA_derived
    \<open>splitting a module by associativity\<close>
 and To_ToA_derived_SDistri = (61, [61,61])
                              for (\<open>x \<Ztypecolon> F st T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F t T \<^emph> F s T \<s>\<u>\<b>\<j> y. r y @action to (\<s>\<p>\<l>\<i>\<t>-\<s>\<c>\<a>\<l>\<a>\<r> s t)\<close>)
                              in To_ToA_derived
    \<open>splitting a module by scalar distributivity\<close>

(*
subsubsection \<open>Guess Algebraic Operators\<close>

\<phi>reasoner_group guess_algebraic_oprs = (100, [0, 3000]) for \<open>_\<close>
    \<open>A general group consisting of reasoning rules derivign or guessing operators for algbebraic properties\<close>
 and guess_algebraic_oprs_default = (1000, [1000, 1030]) for \<open>_\<close> in guess_algebraic_oprs
    \<open>Cutting rules derivign or guessing operators for algbebraic properties\<close>
 and guess_algebraic_oprs_cut = (1000, [1000, 1030]) for \<open>_\<close> in guess_algebraic_oprs
    \<open>Cutting rules derivign or guessing operators for algbebraic properties\<close>
*)



subsubsection \<open>Configurations\<close>

\<phi>reasoner_group Semimodule_No_SDistr = (1000, [1000,1000]) for \<open>Semimodule_No_SDistr F\<close> \<open>\<close>
  
declare [[
  \<phi>default_reasoner_group
      \<open>Tyops_Commute   F F' G G' T D R\<close>        : %\<phi>TA_commutativity_default (100)
      \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r\<close> : %\<phi>TA_commutativity_default (100)
      \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r\<close> : %\<phi>TA_commutativity_default (100)
      \<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>I F F' G G' T D r\<close>        : %\<phi>TA_commutativity_default (100)
      \<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>E F F' G G' T D r\<close>        : %\<phi>TA_commutativity_default (100) ,

  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Transformation_Functor _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Functional_Transformation_Functor _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Transformation_Functor\<^sub>\<Lambda> _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Functional_Transformation_Functor\<^sub>\<Lambda> _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Transformation_BiFunctor _ _ _ _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Functional_Transformation_BiFunctor _ _ _ _ _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Object_Sep_Homo\<^sub>I _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Object_Sep_Homo\<^sub>E _ \<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Separation_Homo\<^sub>I _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Separation_Homo\<^sub>E _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Separation_Homo\<^sub>I_Cond _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Separation_Homo\<^sub>E_Cond _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_Zero _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Closed_Semimodule_Zero _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_One\<^sub>I _ _ _ _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_One\<^sub>E _ _ _ _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_Scalar_Assoc\<^sub>I _ _ _ _ _ _ _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_Scalar_Assoc\<^sub>E _ _ _ _ _ _ _ _ _ \<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_SDistr_Homo\<^sub>Z _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_SDistr_Homo\<^sub>Z_rev _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_SDistr_Homo\<^sub>S _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Semimodule_SDistr_Homo\<^sub>S_rev _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Tyops_Commute _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>I _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>E _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 _ _ _ _ _ _ _ _ _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 _ _ _ _ _ _ _ _ _\<close>,

  \<phi>reason_default_pattern
      \<open>Transformation_Functor ?Fa ?Fb _ _ _ _ _\<close> \<Rightarrow>
      \<open>Transformation_Functor ?Fa _ _ _ _ _ _\<close>
      \<open>Transformation_Functor _ ?Fb _ _ _ _ _\<close>   (100)
  and \<open>Functional_Transformation_Functor ?Fa ?Fb _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Functional_Transformation_Functor ?Fa _ _ _ _ _ _ _\<close>
      \<open>Functional_Transformation_Functor _ ?Fb _ _ _ _ _ _\<close>   (100)
  and \<open>Transformation_Functor\<^sub>\<Lambda> ?Fa ?Fb _ _ _ _ _\<close> \<Rightarrow>
      \<open>Transformation_Functor\<^sub>\<Lambda> ?Fa _ _ _ _ _ _\<close>
      \<open>Transformation_Functor\<^sub>\<Lambda> _ ?Fb _ _ _ _ _\<close>   (100)
  and \<open>Functional_Transformation_Functor\<^sub>\<Lambda> ?Fa ?Fb _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Functional_Transformation_Functor\<^sub>\<Lambda> ?Fa _ _ _ _ _ _ _\<close>
      \<open>Functional_Transformation_Functor\<^sub>\<Lambda> _ ?Fb _ _ _ _ _ _\<close>   (100)
  and \<open>Transformation_BiFunctor ?Fa ?Fb _ _ _ _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Transformation_BiFunctor ?Fa _ _ _ _ _ _ _ _ _ _\<close>
      \<open>Transformation_BiFunctor _ ?Fb _ _ _ _ _ _ _ _ _\<close>   (100)
  and \<open>Functional_Transformation_BiFunctor ?Fa ?Fb _ _ _ _ _ _ _ _ _ _ \<close> \<Rightarrow>
      \<open>Functional_Transformation_BiFunctor ?Fa _ _ _ _ _ _ _ _ _ _ _\<close>
      \<open>Functional_Transformation_BiFunctor _ ?Fb _ _ _ _ _ _ _ _ _ _\<close>   (100)
  and \<open>Separation_Homo\<^sub>I ?Ft ?Fu ?Fc _ _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>I ?Ft _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>I _ ?Fu _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>I _ _ ?Fc _ _ _ _\<close>    (100)
  and \<open>Separation_Homo\<^sub>E ?Ft ?Fu ?Fc _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>E _ _ ?Fc _ _ _\<close>
      \<open>Separation_Homo\<^sub>E _ ?Fu _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>E ?Ft _ _ _ _ _\<close>    (100)
  and \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I ?Ft ?Fu ?Fc _ _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I ?Ft _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I _ ?Fu _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I _ _ ?Fc _ _ _ _\<close>  (100)
  and \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E ?Ft ?Fu ?Fc _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E ?Ft _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E _ ?Fu _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E _ _ ?Fc _ _ _\<close>    (100)
  and \<open>Object_Sep_Homo\<^sub>I ?T _\<close> \<Rightarrow> \<open>Object_Sep_Homo\<^sub>I ?T _\<close> (100)
  and \<open>Separation_Homo\<^sub>I_Cond ?Ft ?Fu ?Fc _ _ _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>I_Cond ?Ft _ _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>I_Cond _ ?Fu _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>I_Cond _ _ ?Fc _ _ _ _ _\<close>  (100)
  and \<open>Separation_Homo\<^sub>E_Cond ?Ft ?Fu ?Fc _ _ _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>E_Cond ?Ft _ _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>E_Cond _ ?Fu _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>E_Cond _ _ ?Fc _ _ _ _ _\<close>  (100)
  and \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond ?Ft ?Fu ?Fc _ _ _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond ?Ft _ _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond _ ?Fu _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond _ _ ?Fc _ _ _ _ _\<close>  (100)
  and \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond ?Ft ?Fu ?Fc _ _ _ _ _\<close> \<Rightarrow>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond ?Ft _ _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond _ ?Fu _ _ _ _ _ _\<close>
      \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond _ _ ?Fc _ _ _ _ _\<close>  (100)
  and \<open>Semimodule_SDistr_Homo\<^sub>Z ?F _ _ _\<close> \<Rightarrow> \<open>Semimodule_SDistr_Homo\<^sub>Z ?F _ _ _\<close> (100)
  and \<open>Semimodule_SDistr_Homo\<^sub>S ?F _ _ _\<close> \<Rightarrow> \<open>Semimodule_SDistr_Homo\<^sub>S ?F _ _ _\<close> (100)
  and \<open>Semimodule_SDistr_Homo\<^sub>Z_rev ?F _ _ _ _ _\<close> \<Rightarrow> \<open>Semimodule_SDistr_Homo\<^sub>Z_rev ?F _ _ _ _ _\<close> (100)
  and \<open>Semimodule_SDistr_Homo\<^sub>S_rev ?F _ _ _ _ _\<close> \<Rightarrow> \<open>Semimodule_SDistr_Homo\<^sub>S_rev ?F _ _ _ _ _\<close> (100)
  and \<open>Semimodule_No_SDistr ?F\<close> \<Rightarrow> \<open>Semimodule_No_SDistr ?F\<close> (100)
  and \<open>Tyops_Commute ?F _ ?G _ ?T _ _\<close> \<Rightarrow> \<open>Tyops_Commute ?F _ ?G _ ?T _ _\<close> (100)
  and \<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>I ?F _ ?G _ ?T _ _\<close> \<Rightarrow> \<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>I ?F _ ?G _ ?T _ _\<close> (100)
  and \<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>E ?F _ ?G _ ?T _ _\<close> \<Rightarrow> \<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>E ?F _ ?G _ ?T _ _\<close> (100)
  and \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?F _ _ ?G _ ?T ?U _ _\<close> \<Rightarrow>
      \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?F _ _ ?G _ ?T ?U _ _\<close>   (100)
  and \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?F _ _ ?G _ ?T ?U _ _\<close> \<Rightarrow>
      \<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?F _ _ ?G _ ?T ?U _ _\<close>   (100)
]]


paragraph \<open>Configuring Property Data Base\<close>

(* hide_fact \<phi>inductive_destruction_rule_from_direct_definition
          \<phi>inductive_destruction_rule_from_direct_definition'
          \<phi>Type_conv_eq_1 \<phi>Type_conv_eq_2 \<phi>intro_transformation *)

setup \<open>
let fun attach_var F =
      let val i = maxidx_of_term F + 1
       in case fastype_of F of \<^Type>\<open>fun T _\<close> => F $ Var(("uu",i),T)
                             | _ => error "Impossible #8da16473-84ef-4bd8-9a96-331bcff88011"
      end
    open PLPR_Template_Properties
in (*Phi_Type.Detection_Rewr.setup_attribute \<^binding>\<open>\<phi>functor_of\<close>
  "set the pattern rewrite to parse the functor part and the argument part from a term\
  \ matching the patter"
#>*)add_property_kinds [
  \<^pattern_prop>\<open>Transformation_Functor _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Functional_Transformation_Functor _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Transformation_Functor\<^sub>\<Lambda> _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Functional_Transformation_Functor\<^sub>\<Lambda> _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Transformation_BiFunctor _ _ _ _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Functional_Transformation_BiFunctor _ _ _ _ _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>I _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>E _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>I_Cond _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>E_Cond _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Closed_Semimodule_Zero _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_Zero _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_One\<^sub>I _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_One\<^sub>E _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_Scalar_Assoc\<^sub>I _ _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_Scalar_Assoc\<^sub>E _ _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_SDistr_Homo\<^sub>Z _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_SDistr_Homo\<^sub>S _ _ _ _\<close>,
  \<^pattern_prop>\<open>Semimodule_No_SDistr _\<close>,
  \<^pattern_prop>\<open>Tyops_Commute _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>I _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Tyops_Commute\<^sub>\<Lambda>\<^sub>E _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 _ _ _ _ _ _ _ _ _\<close>,
  \<^pattern_prop>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 _ _ _ _ _ _ _ _ _\<close>
]

(*#> Phi_Type.add_property_kind \<^const_name>\<open>Object_Equiv\<close> (fn (_ $ T $ _) => T)*)
\<comment> \<open>We do not add Object_Equiv into the property-based template instantiation here because
  it can have special overridings for singular points like that many type operators \<open>F\<close> have a
  wider reachability relation at \<open>F \<circle>\<close>. The overloadings multiply the resulted instantiations
  and they requires priority precedence which is not in the capability of the template
  instantiation automation.\<close>
end
\<close>
  
setup \<open>
PLPR_Template_Properties.add_property_kinds [
  \<^pattern_prop>\<open>TERM (Identity_Elements\<^sub>I _)\<close>,
  \<^pattern_prop>\<open>TERM (Identity_Elements\<^sub>E _)\<close>
]

\<close>

declare [[
  \<phi>reason_default_pattern \<open>TERM (Identity_Elements\<^sub>I ?F)\<close> \<Rightarrow> \<open>TERM (Identity_Elements\<^sub>I ?FF)\<close> (100)
                      and \<open>TERM (Identity_Elements\<^sub>E ?F)\<close> \<Rightarrow> \<open>TERM (Identity_Elements\<^sub>E ?FF)\<close> (100)
]]

text \<open>Candidates of templates instantiation are not prioritized. When a property requires multiple
  rules ordered by their priorities for overrides and optimizations, the property is not declared
  as a parameter property in the template instantiation system but just a \<phi>-LPR reasoning goal tagged
  by \<open>\<A>_template_reason\<close> in the template.
  Instead, a trigger \<open>TERM (The_Property F)\<close> is used as the parameter property activating
  the instantiation and (when the trigger is given) indicating when the prioritized rules are all given
  so when can the instantiation start. \<close>



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


subsubsection \<open>Transformation Bi-Functor\<close>

lemma Transformation_BiFunctor_sub_dom:
  \<open> (\<And>x. D\<^sub>1 x \<subseteq> D\<^sub>1' x)
\<Longrightarrow> (\<And>x. D\<^sub>2 x \<subseteq> D\<^sub>2' x)
\<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper
\<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1' D\<^sub>2' R\<^sub>1 R\<^sub>2 mapper\<close>
  unfolding Transformation_BiFunctor_def
  by (clarsimp simp add: subset_iff; blast)

lemma Transformation_BiFunctor_sub_rng:
  \<open> (\<And>x. R\<^sub>1' x \<subseteq> R\<^sub>1 x)
\<Longrightarrow> (\<And>x. R\<^sub>2' x \<subseteq> R\<^sub>2 x)
\<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1  R\<^sub>2  mapper
\<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1' R\<^sub>2' mapper\<close>
  unfolding Transformation_BiFunctor_def
  by (clarsimp simp add: subset_iff; blast)

lemma Transformation_BiFunctor_sub_mapper:
  \<open> ma \<le> mb
\<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 ma
\<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mb\<close>
  unfolding Transformation_BiFunctor_def le_fun_def Transformation_def
  by (clarsimp simp add: Ball_def; smt (verit, best))

lemma apply_Transformation_BiFunctor:
  \<open> Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper
\<Longrightarrow> (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D\<^sub>1 x \<Longrightarrow> a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b)
\<Longrightarrow> (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D\<^sub>2 x \<Longrightarrow> a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x)
\<Longrightarrow> x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y \<close>
  unfolding Transformation_BiFunctor_def Premise_def
  by simp

lemma apply_Functional_Transformation_BiFunctor:
  \<open> Functional_Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 pred_mapper func_mapper
\<Longrightarrow> (\<And>a \<in> D\<^sub>1 x. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f\<^sub>1 a \<Ztypecolon> U\<^sub>1 \<w>\<i>\<t>\<h> P\<^sub>1 a)
\<Longrightarrow> (\<And>a \<in> D\<^sub>2 x. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f\<^sub>2 a \<Ztypecolon> U\<^sub>2 \<w>\<i>\<t>\<h> P\<^sub>2 a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D\<^sub>1 x \<longrightarrow> f\<^sub>1 a \<in> R\<^sub>1 x) \<and> (\<forall>a. a \<in> D\<^sub>2 x \<longrightarrow> f\<^sub>2 a \<in> R\<^sub>2 x)
\<Longrightarrow> x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<w>\<i>\<t>\<h> pred_mapper f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x\<close>
  unfolding meta_Ball_def Argument_def Premise_def
            Functional_Transformation_BiFunctor_def Transformation_Functor_def
  by clarsimp


subsubsection \<open>Transformation Functor with Parameterization\<close>

lemma Transformation_Functor\<^sub>\<Lambda>_sub_dom:
  \<open> (\<And>p x. Da p x \<subseteq> Db p x)
\<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U Da R mapper
\<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U Db R mapper\<close>
  unfolding Transformation_Functor\<^sub>\<Lambda>_def
  by (clarsimp simp add: subset_iff; blast)

lemma Transformation_Functor\<^sub>\<Lambda>_sub_rng:
  \<open> (\<And>p x. Rb p x \<subseteq> Ra p x)
\<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D Ra mapper
\<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D Rb mapper\<close>
  unfolding Transformation_Functor\<^sub>\<Lambda>_def
  by (clarsimp simp add: subset_iff; blast)

lemma Transformation_Functor\<^sub>\<Lambda>_sub_mapper:
  \<open> ma \<le> mb
\<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R ma
\<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R mb\<close>
  unfolding Transformation_Functor\<^sub>\<Lambda>_def
  by (clarsimp simp add: le_fun_def Transformation_def Ball_def, blast)

lemma apply_Transformation_Functor\<^sub>\<Lambda>:
  \<open> Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R mapper
\<Longrightarrow> (\<And>p a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D p x \<Longrightarrow> a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y \<close>
  unfolding Transformation_Functor\<^sub>\<Lambda>_def Premise_def Transformation_def
  by clarsimp

lemma apply_Functional_Transformation_Functor\<^sub>\<Lambda>:
  \<open> Functional_Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R pred_mapper func_mapper
\<Longrightarrow> (\<And>p. \<And>a \<in> D p x. \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f p a \<Ztypecolon> U p \<w>\<i>\<t>\<h> P p a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>p a. a \<in> D p x \<longrightarrow> f p a \<in> R p x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper f P x\<close>
  unfolding meta_Ball_def Argument_def Premise_def Functional_Transformation_Functor\<^sub>\<Lambda>_def
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

lemma apply_Separation_Homo\<^sub>I_Cond\<^sub>3':
  \<open> Separation_Homo\<^sub>I_Cond F\<^sub>T F\<^sub>U F\<^sub>T\<^sub>U C\<^sub>U T U D\<^sub>1 z\<^sub>1
\<Longrightarrow> Separation_Homo\<^sub>I_Cond F\<^sub>T\<^sub>U F\<^sub>W F\<^sub>3 C\<^sub>W (T \<^emph>[C\<^sub>U] U) W D\<^sub>2 z\<^sub>2
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fst x \<in> D\<^sub>1 \<and> apfst z\<^sub>1 x \<in> D\<^sub>2
\<Longrightarrow> x \<Ztypecolon> (F\<^sub>T T \<^emph>[C\<^sub>U] F\<^sub>U U) \<^emph>[C\<^sub>W] F\<^sub>W W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z\<^sub>2 (apfst z\<^sub>1 x) \<Ztypecolon> F\<^sub>3 ((T \<^emph>[C\<^sub>U] U) \<^emph>[C\<^sub>W] W) \<close>
  unfolding Separation_Homo\<^sub>I_Cond_def Premise_def split_paired_all Transformation_def
  by (cases C\<^sub>U; cases C\<^sub>W; cases x; simp; metis prod.collapse)


lemma apply_Separation_Homo\<^sub>E_Cond:
  \<open> Separation_Homo\<^sub>E_Cond Ft Fu Fc C\<^sub>W T U D un
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph>[C\<^sub>W] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un x \<Ztypecolon> Ft(T) \<^emph>[C\<^sub>W] Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_Cond_def \<phi>Prod_expn'[symmetric] Premise_def
  by simp

paragraph \<open>With Parameterization\<close>

lemma Separation_Homo\<^sub>\<Lambda>\<^sub>I_sub_D:
  \<open> D' \<subseteq> D
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>I F\<^sub>a F\<^sub>b F\<^sub>c T U D  z
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>I F\<^sub>a F\<^sub>b F\<^sub>c T U D' z\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_def
  by blast

lemma Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond_sub_D:
  \<open> D' \<subseteq> D
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond F\<^sub>a F\<^sub>b F\<^sub>c C\<^sub>W T U D  z
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond F\<^sub>a F\<^sub>b F\<^sub>c C\<^sub>W T U D' z\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond_def
  by blast

lemma Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond_sub_D:
  \<open> D' \<subseteq> D
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond F\<^sub>a F\<^sub>b F\<^sub>c C\<^sub>R T U D  z
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond F\<^sub>a F\<^sub>b F\<^sub>c C\<^sub>R T U D' z\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond_def
  by blast

lemma apply_Separation_Homo\<^sub>\<Lambda>\<^sub>I:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>I Ft Fu Fc T U D z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Ft(T) \<^emph> Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z x \<Ztypecolon> Fc(\<lambda>p. T p \<^emph> U p)\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_def Premise_def meta_Ball_def meta_case_prod_def split_paired_all
  by (cases x; simp)

lemma apply_Separation_Homo\<^sub>\<Lambda>\<^sub>E:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>E Ft Fu Fc T U un
\<Longrightarrow> x \<Ztypecolon> Fc(\<lambda>p. T p \<^emph> U p) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un x \<Ztypecolon> Ft(T) \<^emph> Fu(U)\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_def \<phi>Prod_expn'[symmetric]
  by simp

lemma apply_Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond Ft Fu Fc C\<^sub>R T U D z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Ft(T) \<^emph>[C\<^sub>R] Fu(U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z x \<Ztypecolon> Fc(\<lambda>p. T p \<^emph>[C\<^sub>R] U p)\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond_def Premise_def split_paired_all
  by (cases x; simp)

lemma apply_Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond Ft Fu Fc C\<^sub>W T U D un
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D
\<Longrightarrow> x \<Ztypecolon> Fc(\<lambda>p. T p \<^emph>[C\<^sub>W] U p) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> un x \<Ztypecolon> Ft(T) \<^emph>[C\<^sub>W] Fu(U)\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond_def \<phi>Prod_expn'[symmetric] Premise_def
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
\<Longrightarrow> x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fs s (Ft t T) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Premise_def
  by clarsimp


paragraph \<open>Identity Element\<close>

lemma apply_Semimodule_One\<^sub>I:
  \<open> Semimodule_One\<^sub>I F T\<^sub>1 one D f P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F one \<w>\<i>\<t>\<h> P x \<close>
  unfolding Semimodule_One\<^sub>I_def Premise_def
  by simp

lemma apply_Semimodule_One\<^sub>I_\<phi>Some:
  \<open> Semimodule_One\<^sub>I F T\<^sub>1 one D f P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> \<black_circle> F one \<w>\<i>\<t>\<h> P x \<close>
  unfolding Semimodule_One\<^sub>I_def Premise_def \<phi>Some_transformation_strip
  by simp

lemma apply_Semimodule_One\<^sub>E:
  \<open> Semimodule_One\<^sub>E F T\<^sub>1 one D f P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F one \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T\<^sub>1 \<w>\<i>\<t>\<h> P x \<close>
  unfolding Semimodule_One\<^sub>E_def Premise_def
  by simp

lemma apply_Semimodule_One\<^sub>E_\<phi>Some:
  \<open> Semimodule_One\<^sub>E F T\<^sub>1 one D f P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F one \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> \<black_circle> T\<^sub>1 \<w>\<i>\<t>\<h> P x \<close>
  unfolding Semimodule_One\<^sub>E_def Premise_def \<phi>Some_transformation_strip
  by simp


paragraph \<open>Left Distributivity\<close>

lemma Semimodule_SDistr_Homo\<^sub>Z_sub:
  \<open> Ds \<le> Ds' \<and> Dx \<le> Dx'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F Ds' Dx' z
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def le_fun_def le_bool_def
  by blast

lemma [\<phi>adding_property = false,
       \<phi>reason %\<phi>TA_varify_out except \<open>Semimodule_SDistr_Homo\<^sub>Z _ ?var_Ds ?var_Dx _\<close>,
       \<phi>adding_property = true ]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds' Dx' z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds \<le> Ds' \<and> Dx \<le> Dx'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z\<close>
  unfolding Premise_def
  using Semimodule_SDistr_Homo\<^sub>Z_sub by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>Z:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> F t \<^emph> F s \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> F (s + t) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Premise_def
  by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F t \<^emph> \<black_circle> F s \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s x \<Ztypecolon> \<black_circle> F (s + t) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Premise_def Transformation_def
  by (clarsimp; metis prod.collapse)

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_RCond_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (C \<longrightarrow> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x) \<and> ?\<^sub>+ True r = ?\<^sub>+ C s + ?\<^sub>+ True t
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F t \<^emph> \<half_blkcirc>[C] F s \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?\<^sub>j\<^sub>R C (z t s) x \<Ztypecolon> \<black_circle> F r \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Premise_def Transformation_def
  by (cases C; clarsimp; metis prod.collapse)

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_LCond_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (C \<longrightarrow> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x) \<and> ?\<^sub>+ True r = ?\<^sub>+ True s + ?\<^sub>+ C t
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[C] F t \<^emph> \<black_circle> F s \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?\<^sub>j\<^sub>L C (z t s) x \<Ztypecolon> \<black_circle> F r \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Premise_def Transformation_def
  by (cases C; clarsimp; metis prod.collapse)

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_rev:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx' z'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F Ds Dx' z' Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> F s \<^emph> F t \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> F (s + t) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_rev_def Premise_def
  by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_rev_LCond_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx' z'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F Ds Dx' z' Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (C \<longrightarrow> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x) \<and> ?\<^sub>+ True r = ?\<^sub>+ True s + ?\<^sub>+ C t
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F s \<^emph> \<half_blkcirc>[C] F t \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?\<^sub>j\<^sub>R C (z s t) x \<Ztypecolon> \<black_circle> F r \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Premise_def Transformation_def
            Semimodule_SDistr_Homo\<^sub>Z_rev_def
  by (cases C; clarsimp; metis prod.collapse)

lemma apply_Semimodule_SDistr_Homo\<^sub>Z_rev_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx' z'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F Ds Dx' z' Dx z
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F s \<^emph> \<black_circle> F t \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z s t x \<Ztypecolon> \<black_circle> F (s + t) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_rev_def Premise_def Transformation_def
  by (clarsimp; metis prod.collapse)

lemma apply_Semimodule_SDistr_Homo\<^sub>S:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> F (s + t) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t \<^emph> F s \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_def Premise_def
  by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F (s + t) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> \<black_circle> F t \<^emph> \<black_circle> F s \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_def Premise_def Transformation_def
  by (clarsimp; metis sep_disj_option(1) times_option(1))

lemma apply_Semimodule_SDistr_Homo\<^sub>S_RCond_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (C \<longrightarrow> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x) \<and>
           ?\<^sub>+ True r = ?\<^sub>+ C s + ?\<^sub>+ True t
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F r \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?\<^sub>s\<^sub>R C (uz t s) x \<Ztypecolon> \<black_circle> F t \<^emph> \<half_blkcirc>[C] F s \<close>
  unfolding Premise_def Semimodule_SDistr_Homo\<^sub>S_def Transformation_def
  by (cases C; clarsimp; metis sep_disj_option(1) times_option(1))

lemma apply_Semimodule_SDistr_Homo\<^sub>S_LCond_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (C \<longrightarrow> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x) \<and>
           ?\<^sub>+ True r = ?\<^sub>+ True s + ?\<^sub>+ C t
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F r \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?\<^sub>s\<^sub>L C (uz t s) x \<Ztypecolon> \<half_blkcirc>[C] F t \<^emph> \<black_circle> F s \<close>
  unfolding Premise_def Semimodule_SDistr_Homo\<^sub>S_def Transformation_def
  by (cases C; clarsimp; metis sep_disj_option(1) times_option(1))

lemma apply_Semimodule_SDistr_Homo\<^sub>S_rev:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx' uz'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S_rev F Dx' uz' Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> F (s + t) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F s \<^emph> F t \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_rev_def Premise_def
  by blast

lemma apply_Semimodule_SDistr_Homo\<^sub>S_rev_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx' uz'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S_rev F Dx' uz' Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F (s + t) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> \<black_circle> F s \<^emph> \<black_circle> F t \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_rev_def Premise_def Transformation_def
  by (clarsimp; metis sep_disj_option(1) times_option(1))

lemma apply_Semimodule_SDistr_Homo\<^sub>S_rev_RCond_\<phi>Some:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx' uz'
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S_rev F Dx' uz' Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (C \<longrightarrow> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x) \<and> ?\<^sub>+ True r = ?\<^sub>+ True s + ?\<^sub>+ C t
\<Longrightarrow> x \<Ztypecolon> \<black_circle> F r \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?\<^sub>s\<^sub>R C (uz s t) x \<Ztypecolon> \<black_circle> F s \<^emph> \<half_blkcirc>[C] F t \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_def Semimodule_SDistr_Homo\<^sub>S_rev_def Premise_def Transformation_def
  by (cases C; clarsimp; metis sep_disj_option(1) times_option(1))


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


subsubsection \<open>Swap \& Assoc Normalization\<close>

\<phi>reasoner_group \<phi>ToA_SA_norm = (1000, [10,2000]) in \<phi>simp
      \<open>normalize the \<phi>-type by swapping, as that specified by \<open>\<phi>ToA_swap_normalization\<close>\<close>
  and \<phi>ToA_SA_derived = (50, [50, 50]) in \<phi>simp_derived and in \<phi>ToA_SA_norm
                                              and > \<phi>simp_derived_Tr_functor
      \<open>derived\<close>


ML_file \<open>library/phi_type_algebra/commutativity.ML\<close>
(*ML_file \<open>library/phi_type_algebra/weight.ML\<close>*)

definition Require_Swap_Norm :: \<open>('c,'a) \<phi> \<Rightarrow> bool\<close>
  where \<open>Require_Swap_Norm F_G_T \<equiv> True\<close>
    \<comment> \<open>a pure syntactical checking for whether \<open>F\<close> should be swapped into \<open>G\<close>, in \<open>F(G(T))\<close>,
        or any multi-arity version\<close>

definition Not_Require_Swap_Norm :: \<open>('c,'a) \<phi> \<Rightarrow> bool\<close>
  where \<open>Not_Require_Swap_Norm F_G_T \<equiv> True\<close>

definition Require_Assoc_Norm :: \<open>('c,'a) \<phi> \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Require_Assoc_Norm F_G_T direction \<equiv> True\<close>
  \<comment> \<open>\<open>direction = True\<close> for using intro rules only ; \<open>False\<close> for elim rules only\<close>

definition Not_Require_Assoc_Norm :: \<open>('c,'a) \<phi> \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Not_Require_Assoc_Norm F_G_T direction \<equiv> True\<close>

definition Require_SA_Norm :: \<open>('c,'a) \<phi> \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Require_SA_Norm F_G_T direction \<equiv> Require_Swap_Norm F_G_T \<or> Require_Assoc_Norm F_G_T direction \<close>

definition Not_Require_SA_Norm :: \<open>('c,'a) \<phi> \<Rightarrow> bool \<Rightarrow> bool\<close>
  where \<open>Not_Require_SA_Norm F_G_T direction \<equiv> Not_Require_Swap_Norm F_G_T \<and> Not_Require_Assoc_Norm F_G_T direction \<close>
  

\<phi>reasoner_ML Require_Swap_Norm %cutting (\<open>Require_Swap_Norm _\<close>) = \<open> fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (bvs, F_G_T) =
        case Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
          of (bvtys, _ (*Trueprop*) $ (Const _ (*Require_Swap_Norm*) $ F_G_T)) =>
             (bvtys, F_G_T)
   in if Phi_Type.whether_to_swap_normalize (Context.Proof ctxt) bvs F_G_T
      then SOME ((ctxt, @{lemma' \<open>Require_Swap_Norm F\<close> by (simp add: Require_Swap_Norm_def)} RS sequent), Seq.empty)
      else NONE
  end)
\<close>

\<phi>reasoner_ML Not_Require_Swap_Norm %cutting (\<open>Not_Require_Swap_Norm _\<close>) = \<open> fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (bvs, F_G_T) =
        case Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
          of (bvtys, _ (*Trueprop*) $ (Const _ (*Not_Require_Swap_Norm*) $ F_G_T)) =>
             (bvtys, F_G_T)
   in if Phi_Type.whether_to_swap_normalize (Context.Proof ctxt) bvs F_G_T
      then NONE
      else SOME ((ctxt, @{lemma' \<open>Not_Require_Swap_Norm F\<close> by (simp add: Not_Require_Swap_Norm_def)} RS sequent), Seq.empty)
  end)
\<close>

\<phi>reasoner_ML Require_Assoc_Norm %cutting (\<open>Require_Assoc_Norm _ _\<close>) = \<open> fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (bvs, F_G_T, direction) =
        case Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
          of (bvtys, _ (*Trueprop*) $ (Const _ (*Require_Swap_Norm*) $ F_G_T $ direction)) =>
             (bvtys, F_G_T, (case direction of \<^Const>\<open>True\<close> => Phi_Type.AD_INTRO
                                             | \<^Const>\<open>False\<close> => Phi_Type.AD_ELIM
                                             | _ => raise TERM ("Bad direction of Require_Assoc_Norm", [direction])))
   in if Phi_Type.whether_to_assoc_normalize (Context.Proof ctxt) direction bvs F_G_T
      then SOME ((ctxt, @{lemma' \<open>Require_Assoc_Norm F Any\<close> by (simp add: Require_Assoc_Norm_def)} RS sequent), Seq.empty)
      else NONE
  end)
\<close>

\<phi>reasoner_ML Not_Require_Assoc_Norm %cutting (\<open>Not_Require_Assoc_Norm _ _\<close>) = \<open> fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (bvs, F_G_T, direction) =
        case Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
          of (bvtys, _ (*Trueprop*) $ (Const _ (*Require_Swap_Norm*) $ F_G_T $ direction)) =>
             (bvtys, F_G_T, (case direction of \<^Const>\<open>True\<close> => Phi_Type.AD_INTRO
                                             | \<^Const>\<open>False\<close> => Phi_Type.AD_ELIM
                                             | _ => raise TERM ("Bad direction of Require_Assoc_Norm", [direction])))
   in if Phi_Type.whether_to_assoc_normalize (Context.Proof ctxt) direction bvs F_G_T
      then NONE
      else SOME ((ctxt, @{lemma' \<open>Not_Require_Assoc_Norm F Any\<close> by (simp add: Not_Require_Assoc_Norm_def)} RS sequent), Seq.empty)
  end)
\<close>

\<phi>reasoner_ML Require_SA_Norm %cutting (\<open>Require_SA_Norm _ _\<close>) = \<open> fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (bvs, F_G_T, direction) =
        case Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
          of (bvtys, _ (*Trueprop*) $ (Const _ (*Require_Swap_Norm*) $ F_G_T $ direction)) =>
             (bvtys, F_G_T, (case direction of \<^Const>\<open>True\<close> => Phi_Type.AD_INTRO
                                             | \<^Const>\<open>False\<close> => Phi_Type.AD_ELIM
                                             | _ => raise TERM ("Bad direction of Require_SA_Norm", [direction])))
   in if Phi_Type.whether_to_SA_normalize (Context.Proof ctxt) direction bvs F_G_T
      then SOME ((ctxt, @{lemma' \<open>Require_SA_Norm F Any\<close>
                             by (simp add: Require_SA_Norm_def Require_Assoc_Norm_def )} RS sequent), Seq.empty)
      else NONE
  end)
\<close>

\<phi>reasoner_ML Not_Require_SA_Norm %cutting (\<open>Not_Require_SA_Norm _ _\<close>) = \<open> fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let val (bvs, F_G_T, direction) =
        case Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
          of (bvtys, _ (*Trueprop*) $ (Const _ (*Require_Swap_Norm*) $ F_G_T $ direction)) =>
             (bvtys, F_G_T, (case direction of \<^Const>\<open>True\<close> => Phi_Type.AD_INTRO
                                             | \<^Const>\<open>False\<close> => Phi_Type.AD_ELIM
                                             | _ => raise TERM ("Bad direction of Not_Require_SA_Norm", [direction])))
   in if Phi_Type.whether_to_SA_normalize (Context.Proof ctxt) direction bvs F_G_T
      then NONE
      else SOME ((ctxt, @{lemma' \<open>Not_Require_SA_Norm F Any\<close>
                             by (simp add: Not_Require_SA_Norm_def Not_Require_Assoc_Norm_def Not_Require_Swap_Norm_def )}
                        RS sequent), Seq.empty)
  end)
\<close>


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

lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>x g\<^sub>1 g\<^sub>2.
            \<forall>a \<in> D\<^sub>1 x. a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b
        \<Longrightarrow> \<forall>a \<in> D\<^sub>2 x. a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b
        \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x)
        \<Longrightarrow> x \<Ztypecolon> F1 T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F2 U\<^sub>1 U\<^sub>2 \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Transformation_BiFunctor_def Premise_def
            Transformation_def
  by (simp add: atomize_imp atomize_all)


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
          \<Longrightarrow> (y \<Ztypecolon> F s) * (x \<Ztypecolon> F t) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z t s (x,y) \<Ztypecolon> F (s + t)
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z)) MM DD RR FF\<close>
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
          \<Longrightarrow> x \<Ztypecolon> F (s + t) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> F t \<^emph> F s
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_SDistr_Homo\<^sub>S_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')

(* all be deduced from \<open>Semimodule_SDistr_Homo\<^sub>Z\<close> and no need to go to programming
lemma [\<phi>reason %\<phi>programming_method]:
  \<open> PROP \<phi>Programming_Method (\<And>s t x.
              \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx s t x
          \<Longrightarrow> x \<Ztypecolon> F (s + t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz s t x \<Ztypecolon> F s T \<^emph> F t T
        ) MM DD RR FF
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Semimodule_SDistr_Homo\<^sub>S_rev F T Ds Dx uz)) MM DD RR FF\<close>
  unfolding \<phi>Programming_Method_def Semimodule_SDistr_Homo\<^sub>S_rev_def Premise_def norm_hhf_eq
  by (clarsimp simp add: \<phi>Prod_expn')
*)



section \<open>Definition and Deriving Tools for \<phi>-Types\<close>

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

subsection \<open>Implementation\<close>

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

subparagraph \<open>Intro and Elim reasoning rules\<close>

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


subparagraph \<open>OPEN and MAKE\<close>

text \<open>No \<open>Object_Equiv\<close> is used and we use \<open>(=)\<close> directly because we are destructing or constructing
  a \<phi>-type abstraction by its definition where the definition covers every cases covered by the
  \<open>Object_Equiv\<close>, so there is no need to apply \<open>Object_Equiv\<close> any more.\<close>

lemma \<phi>open_abstraction_infer:
  \<open> (x \<Ztypecolon> T) = (y' \<Ztypecolon> U')
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x' = x
\<Longrightarrow> x' \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U' \<s>\<u>\<b>\<j> y. y = y' @action to (OPEN i T) \<close>
  unfolding Action_Tag_def Simplify_def \<r>Guard_def Premise_def
  by simp

lemma \<phi>open_abstraction_specified:
  \<open> (x \<Ztypecolon> T) = (y' \<Ztypecolon> U')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x' = x
\<Longrightarrow> x' \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U' \<s>\<u>\<b>\<j> y. y = y' @action to (OPEN i T) \<close>
  unfolding Action_Tag_def Simplify_def \<r>Guard_def Premise_def
  by simp


lemma \<phi>open_abstraction_ToA_infer:
  \<open> (x' \<Ztypecolon> T) = U
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = x'
\<Longrightarrow> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> OPEN i T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def Premise_def Orelse_shortcut_def \<r>Guard_def
  by simp

lemma \<phi>open_abstraction_ToA_specified:
  \<open> (x' \<Ztypecolon> T) = U
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x = x'
\<Longrightarrow> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> OPEN i T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def Premise_def Orelse_shortcut_def
  by simp

lemma \<phi>open_abstraction_ToA_R_infer:
  \<open> (x' \<Ztypecolon> T) = U
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = x'
\<Longrightarrow> R * U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (x \<Ztypecolon> OPEN i T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def Premise_def Orelse_shortcut_def \<r>Guard_def
  by simp

lemma \<phi>open_abstraction_ToA_R_specified:
  \<open> (x' \<Ztypecolon> T) = U
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x = x'
\<Longrightarrow> R * U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (x \<Ztypecolon> OPEN i T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def Premise_def Orelse_shortcut_def \<r>Guard_def
  by simp

lemma \<phi>open_abstraction_ToA_W_infer:
  \<open> (x' \<Ztypecolon> T) = (y \<Ztypecolon> U')
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> fst x = x'
\<Longrightarrow> (y, snd x) \<Ztypecolon> U' \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> OPEN i T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def Premise_def Orelse_shortcut_def \<r>Guard_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn')

lemma \<phi>open_abstraction_ToA_W_specified:
  \<open> (x' \<Ztypecolon> T) = (y \<Ztypecolon> U')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fst x = x'
\<Longrightarrow> (y, snd x) \<Ztypecolon> U' \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> OPEN i T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  unfolding OPEN_def Premise_def Orelse_shortcut_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn')





lemma \<phi>make_abstraction_infer:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = x'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = x' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> MAKE i T \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Premise_def Transformation_def MAKE_def \<r>Guard_def Ant_Seq_def
            Orelse_shortcut_def
  by clarsimp

lemma \<phi>make_abstraction_specified:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x = x'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = x' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> MAKE i T \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Premise_def Transformation_def MAKE_def \<r>Guard_def Ant_Seq_def
            Orelse_shortcut_def
  by clarsimp

lemma \<phi>make_abstraction'R_infer:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = x'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = x' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> MAKE i T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Premise_def Transformation_def MAKE_def \<r>Guard_def Ant_Seq_def
            Orelse_shortcut_def
  by (cases C; clarsimp; blast)

lemma \<phi>make_abstraction'R_specified:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x = x'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = x' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> MAKE i T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Premise_def Transformation_def MAKE_def \<r>Guard_def Ant_Seq_def
            Orelse_shortcut_def
  by (cases C; clarsimp; blast)

lemma \<phi>make_abstraction'Rt_infer:
  \<open> (x' \<Ztypecolon> T) = (y \<Ztypecolon> U)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> fst x = x'
    \<comment> \<open>Interesting, here \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[MODE_SAT] fst x = x'\<close> is actually stronger than \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> fst x = x'\<close>
        because the \<open>fst x\<close> can be a schematic variable so \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> fst x = x'\<close> always returns even
        when the instantiating of \<open>fst x\<close> makes the entire sequent inconsistent but \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>\<close> just
        has no way to recognize this.\<close>
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> fst x = x' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, snd x) \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE i T \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Premise_def Transformation_def MAKE_def \<r>Guard_def Ant_Seq_def
            Orelse_shortcut_def MAKE_def
  by (cases C; clarsimp; blast)

lemma \<phi>make_abstraction'Rt_specified:
  \<open> (x' \<Ztypecolon> T) = (y \<Ztypecolon> U)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> fst x = x'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> fst x = x' \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, snd x) \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> MAKE i T \<^emph>[C] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Object_Equiv_def Premise_def Transformation_def MAKE_def \<r>Guard_def Ant_Seq_def
            Orelse_shortcut_def
  by (cases C; clarsimp; blast)


(*
lemma \<phi>make_Identity_Element\<^sub>E:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> Identity_Element\<^sub>E U
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> MAKE T) \<close>
  unfolding MAKE_def
  by simp
*)

lemma \<phi>gen_expansion:
  \<open> (x \<Ztypecolon> T) = U
\<Longrightarrow> p \<Turnstile> (x \<Ztypecolon> T) \<equiv> p \<Turnstile> U \<close>
  by simp

ML_file \<open>library/phi_type_algebra/typ_def.ML\<close>

(*TODO: move*)

consts under_\<phi>deriving :: mode

\<phi>reasoner_ML under_\<phi>deriving %cutting (\<open>True @action under_\<phi>deriving\<close>) = \<open>
  fn (_, (ctxt,sequent)) => Seq.make (fn () =>
      if Config.get ctxt Phi_Type.under_deriving_ctxt
      then SOME ((ctxt, @{lemma' \<open>True @action under_\<phi>deriving\<close>
                             by (simp add: Action_Tag_def)} RS sequent), Seq.empty)
      else NONE)  
\<close>

\<phi>reasoner_ML \<open>Premise under_\<phi>deriving\<close> %cutting (\<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] _\<close>) = \<open>
  fn (_, (ctxt, sequent)) => Seq.make (fn () =>
      if Config.get ctxt Phi_Type.under_deriving_ctxt
      then SOME ((ctxt, @{lemma' \<open>\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] P\<close>
                             by (simp add: Premise_def)} RS sequent), Seq.empty)
      else SOME ((ctxt, @{lemma' \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P \<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] P\<close>
                             by (simp add: Premise_def)} RS sequent), Seq.empty))
\<close>

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>EIF (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] P) P \<close>
  unfolding \<r>EIF_def Premise_def
  by blast

lemma [\<phi>reason %extract_pure]:
  \<open> \<r>ESC P (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[under_\<phi>deriving] P) \<close>
  unfolding \<r>ESC_def Premise_def
  by blast


subsection \<open>Instances for Predefined Basic \<phi>-Types\<close>

text \<open>The section manually gives property instances of predefined basic \<phi>-types and any later \<phi>-types
      are defined using \<phi>-type definition tools and their property instances are derived by derivers.

  Though the property instances of the basic \<phi>-types are given manually here, it does not mean they
  are primitive and cannot be derived automatically. It is just engineeringly, the types are bootstraps
  given very early in the initiation process of the system, so have no chance to enjoy the automation of
  deriver tools and because some properties of them are given manually early, the remaining properties
  also cannot be configured using the deriver tool otherwise clashes happen.
\<close>



section \<open>Applications of the Algebraic Properties in Reasoning\<close>

subsection \<open>Vary Type Operator among Instantiations\<close>

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

definition Type_Variant_of_the_Same_Scalar_Mul\<^sub>0
        :: \<open> ('s \<Rightarrow> ('b,'c) \<phi>) \<Rightarrow> ('s2 \<Rightarrow> ('b2,'c2) \<phi>) \<Rightarrow> bool \<close>
  where \<open> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 Fa Fb \<longleftrightarrow> True \<close>

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
      \<open>Type_Variant_of_the_Same_Type_Operator ?Fa ?Fb\<close> \<Rightarrow>
      \<open>Type_Variant_of_the_Same_Type_Operator ?Fa _\<close>
      \<open>Type_Variant_of_the_Same_Type_Operator _ ?Fb\<close>    (100)
  and \<open>Type_Variant_of_the_Same_Type_Operator2 ?Fa ?Fb\<close> \<Rightarrow>
      \<open>Type_Variant_of_the_Same_Type_Operator2 ?Fa _\<close>
      \<open>Type_Variant_of_the_Same_Type_Operator2 _ ?Fb\<close>   (100)
  and \<open>Type_Variant_of_the_Same_Scalar_Mul ?Fa ?Fb\<close> \<Rightarrow>
      \<open>Type_Variant_of_the_Same_Scalar_Mul ?Fa _\<close>
      \<open>Type_Variant_of_the_Same_Scalar_Mul _ ?Fb\<close>       (100)
  and \<open>Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 ?Fa ?Fb\<close> \<Rightarrow>
      \<open>Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 ?Fa _\<close>
      \<open>Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 _ ?Fb\<close>      (100)
  and \<open>Parameter_Variant_of_the_Same_Type ?Fa ?Fb\<close> \<Rightarrow>
      \<open>Parameter_Variant_of_the_Same_Type ?Fa _\<close>
      \<open>Parameter_Variant_of_the_Same_Type _ ?Fb\<close>        (100)
  (*and \<open>Parameter_Variant_of_the_Same_Type1 ?Fa _\<close> \<Rightarrow> \<open>Parameter_Variant_of_the_Same_Type1 ?Fa _\<close> (100)*)
  
  (* \<phi>premise_attribute? [\<phi>reason add] for \<open>Type_Variant_of_the_Same_Type_Operator _ _\<close> *)
  (* \<phi>premise_attribute? [\<phi>reason add] for \<open>Parameter_Variant_of_the_Same_Type _ _\<close> *)
]]

\<phi>reasoner_group variants_of_type_opr = (%cutting, [%cutting, %cutting])
    for (\<open>Type_Variant_of_the_Same_Type_Operator F F'\<close>,
         \<open>Type_Variant_of_the_Same_Type_Operator2 F F'\<close>,
         \<open>Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F F'\<close>,
         \<open>Type_Variant_of_the_Same_Scalar_Mul F F'\<close>,
         \<open>Parameter_Variant_of_the_Same_Type F F'\<close>)
    \<open>variants_of_type_opr\<close>
  and variants_of_type_opr_overrided = (%cutting+10, [%cutting+10, %cutting+10]) > variants_of_type_opr \<open>\<close>

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

lemma Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_I:
  \<open>Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 Fa Fb\<close>
  unfolding Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def ..

lemma Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_I':
  \<open> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 (\<lambda>s. Fa s T) (\<lambda>s. Fb s U) \<close>
  unfolding Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def ..

                    
ML_file \<open>library/phi_type_algebra/variant_phi_type_instantiations.ML\<close>

setup \<open>
   PLPR_Template_Properties.add_property_kinds [
    \<^pattern_prop>\<open>Type_Variant_of_the_Same_Type_Operator _ _\<close>,
    \<^pattern_prop>\<open>Type_Variant_of_the_Same_Type_Operator2 _ _\<close>,
    \<^pattern_prop>\<open>Type_Variant_of_the_Same_Scalar_Mul _ _\<close>,
    \<^pattern_prop>\<open>Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 _ _\<close>,
    \<^pattern_prop>\<open>Parameter_Variant_of_the_Same_Type _ _\<close>
  (*\<^pattern_prop>\<open>Parameter_Variant_of_the_Same_Type1 _ _\<close>*)
  ]
\<close>

\<phi>reasoner_ML Parameter_Variant_of_the_Same_Type %variants_of_type_opr_overrided (\<open>Parameter_Variant_of_the_Same_Type _ ?var\<close>) = \<open>
  fn (_, (ctxt, sequent)) => Seq.make (fn () =>
    let val (bvtys, goal) = Phi_Help.strip_meta_hhf_bvtys (Phi_Help.leading_antecedent' sequent)
        val _ (*Trueprop*) $ (_ (*Parameter_Variant_of_the_Same_Type*) $ LHS $ var) = goal
        val thy = Proof_Context.theory_of ctxt
        val (Var (v, _), bargs) = strip_comb var
        val barg_tys = map (fn x => fastype_of1 (bvtys, x)) bargs
        exception Not_A_Phi_Type
        fun parse lv bvs (X $ Bound i) =
              if i < lv then parse lv (SOME i :: bvs) X else parse lv (NONE :: bvs) X
          | parse lv bvs (X $ Y) = parse lv (NONE :: bvs) X
          | parse lv bvs (Abs(_,_,X)) = parse (lv+1) (map (Option.map (fn i=>i+1)) bvs) X
          | parse lv bvs (Const(N, _)) =
              let val idx = Thm.maxidx_of sequent + 1
                  val ty = Logic.incr_tvar idx (Sign.the_const_type thy N )
                  val args = List.take (Term.binder_types ty, length bvs)
                  val a_num = length args
                  val b_num = length barg_tys
                  val parameterize = fold_index (fn (i,_) => fn X => X $ Bound (a_num+b_num-1-i)) barg_tys
                  val const = Const(N, ty)
                  val (F0,bvs) = fold_index (
                        fn (_, (SOME b, ty)) => (fn (X,bvs) => (X $ Bound b, (b,ty)::bvs))
                         | (i, (NONE, ty)) => (fn (X,bvs) => (X $ parameterize (Var (("x",idx+i), barg_tys ---> ty)), bvs))
                      ) (bvs ~~ args) (const, [])
                  val F = fold_index (fn (i,_) => fn X =>
                            case AList.lookup (op =) bvs i
                              of SOME ty => Abs ("_", ty, X)
                               | NONE => raise Not_A_Phi_Type
                          ) bvs F0
                       |> fold_rev (fn ty => fn X => Abs ("_", ty, X)) barg_tys
                       |> Thm.cterm_of ctxt
               in Drule.infer_instantiate ctxt [(v, F)] sequent
               |> (fn th => @{lemma' \<open>Parameter_Variant_of_the_Same_Type A B\<close>
                                  by (simp add: Parameter_Variant_of_the_Same_Type_def)} RS th)
               |> (fn th => SOME ((ctxt,th), Seq.empty))
              end
     in parse 0 [] LHS
    end
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

subsection \<open>Transformation Functor\<close>

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

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor name Fa.To_Transformation]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor Fa Fb T U D R mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (Fb Z) \<close>
  unfolding Action_Tag_def \<r>Guard_def
  using transformation[unfolded \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor_fuzzy name Fa.To_Transformation_fuzzy]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> NO_MATCH TYPE('c\<^sub>a\<^sub>a) TYPE('c))
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Transformation_Functor Fa Fb T U D R mapper
\<Longrightarrow> (\<And>a \<in> D x. a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to Z
    <except-pattern> (XX::'c\<^sub>a\<^sub>a BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YY \<w>\<i>\<t>\<h> PP @action to Z \<close>
  for Fa :: \<open>('c\<^sub>a, 'a\<^sub>a) \<phi> \<Rightarrow> ('c,'a) \<phi>\<close> and Z :: \<open>('c\<^sub>a\<^sub>a, 'a\<^sub>a\<^sub>a) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def Except_Pattern_def
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
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (\<forall>a \<in> D x. (a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action \<A>simp))
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>_transitive_simp \<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  using transformation[unfolded atomize_Ball Premise_def \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [\<phi>reason_template name Fa.\<A>backward_simp [\<phi>transformation_based_backward_simp default %\<phi>simp_derived_Tr_functor no trigger]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor Fa Fb T U D R mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (\<forall>a \<in> D x. (a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action \<A>backward_simp))
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>_backward_transitive_simp \<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  using transformation[unfolded atomize_Ball Premise_def \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

  thm meta_Ball_def
  thm ballE


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

lemma [no_atp, \<phi>reason_template default %ToA_derived_one_to_one_functor name Fa.functional_transformation]:
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

subsection \<open>Bi-Transformation Functor\<close>

lemma bitransformation[\<phi>reason_template name Fa.bitransformation []]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper
\<Longrightarrow> (\<And>a \<in> D\<^sub>1 x. a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b)
\<Longrightarrow> (\<And>a \<in> D\<^sub>2 x. a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x)
\<Longrightarrow> x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2  \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y\<close>
  unfolding meta_Ball_def Premise_def \<r>Guard_def Transformation_BiFunctor_def
            Transformation_def
  by clarsimp

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor name Fa.To_BiTransformation]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper
\<Longrightarrow> (\<And>a \<in> D\<^sub>1 x. a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b @action to Z\<^sub>1)
\<Longrightarrow> (\<And>a \<in> D\<^sub>2 x. a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b @action to Z\<^sub>2)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x)
\<Longrightarrow> x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y @action to (Fb Z\<^sub>1 Z\<^sub>2) \<close>
  unfolding Action_Tag_def \<r>Guard_def
  using bitransformation[unfolded \<r>Guard_def, where Fa=Fa and Fb=Fb and D\<^sub>1=D\<^sub>1 and D\<^sub>2=D\<^sub>2 and mapper=mapper] .

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor name Fa.to_bitraverse]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper
\<Longrightarrow> (\<And>a \<in> D\<^sub>1 x. a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z\<^sub>1))
\<Longrightarrow> (\<And>a \<in> D\<^sub>2 x. a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z\<^sub>2))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x)
\<Longrightarrow> x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Fb Z\<^sub>1 Z\<^sub>2) \<close>
  unfolding Action_Tag_def \<r>Guard_def
  using bitransformation[unfolded \<r>Guard_def, where Fa=Fa and Fb=Fb and D\<^sub>1=D\<^sub>1 and D\<^sub>2=D\<^sub>2 and mapper=mapper] .

lemma [\<phi>reason_template name Fa.\<A>simp_bi [\<phi>transformation_based_simp default %\<phi>simp_derived_Tr_functor no trigger]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (\<forall>a \<in> D\<^sub>1 x. (a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b @action \<A>simp))
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (\<forall>a \<in> D\<^sub>2 x. (a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b @action \<A>simp))
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x)
\<Longrightarrow> x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y @action \<A>_transitive_simp \<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  using bitransformation[unfolded atomize_Ball \<r>Guard_def Premise_def, where Fa=Fa and Fb=Fb and D\<^sub>1=D\<^sub>1 and D\<^sub>2=D\<^sub>2 and mapper=mapper] .

lemma [\<phi>reason_template name Fa.\<A>backward_simp_bi [\<phi>transformation_based_backward_simp default %\<phi>simp_derived_Tr_functor no trigger]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (\<forall>a \<in> D\<^sub>1 x. (a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b @action \<A>backward_simp))
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (\<forall>a \<in> D\<^sub>2 x. (a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b @action \<A>backward_simp))
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x)
\<Longrightarrow> x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y @action \<A>_backward_transitive_simp \<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  using bitransformation[unfolded atomize_Ball \<r>Guard_def Premise_def, where Fa=Fa and Fb=Fb and D\<^sub>1=D\<^sub>1 and D\<^sub>2=D\<^sub>2 and mapper=mapper] .


lemma [no_atp, \<phi>reason_template default %ToA_derived_one_to_one_functor name Fa.functional_transformation]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_BiFunctor Fa Fb T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 pred_mapper func_mapper
\<Longrightarrow> (\<And>a \<in> D\<^sub>1 x. a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f\<^sub>1 a \<Ztypecolon> U\<^sub>1 \<w>\<i>\<t>\<h> P\<^sub>1 a)
\<Longrightarrow> (\<And>a \<in> D\<^sub>2 x. a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f\<^sub>2 a \<Ztypecolon> U\<^sub>2 \<w>\<i>\<t>\<h> P\<^sub>2 a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D\<^sub>1 x \<longrightarrow> f\<^sub>1 a \<in> R\<^sub>1 x) \<and> (\<forall>a. a \<in> D\<^sub>2 x \<longrightarrow> f\<^sub>2 a \<in> R\<^sub>2 x)
\<Longrightarrow> x \<Ztypecolon> Fa T\<^sub>1 T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x \<Ztypecolon> Fb U\<^sub>1 U\<^sub>2 \<w>\<i>\<t>\<h> pred_mapper f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x\<close>
  unfolding \<r>Guard_def
  using apply_Functional_Transformation_BiFunctor[unfolded Argument_def,
            where func_mapper=func_mapper and pred_mapper=pred_mapper] .


subsection \<open>Transformation Functor with Parameterization\<close>

lemma transformation\<^sub>\<Lambda>[\<phi>reason_template name Fa.transformation []]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R mapper
\<Longrightarrow> (\<And>p. \<And>a \<in> D p x. a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y\<close>
  unfolding meta_Ball_def Premise_def \<r>Guard_def Transformation_Functor\<^sub>\<Lambda>_def
  by clarsimp

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor name Fa.To_Transformation]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R mapper
\<Longrightarrow> (\<And>p. \<And>a \<in> D p x. a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b @action to (Z p))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (Fb Z) \<close>
  unfolding Action_Tag_def \<r>Guard_def
  using transformation\<^sub>\<Lambda>[unfolded \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor_fuzzy name Fa.To_Transformation_fuzzy]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> NO_MATCH TYPE('c\<^sub>a\<^sub>a) TYPE('c))
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R mapper
\<Longrightarrow> (\<And>p. \<And>a \<in> D p x. a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b @action to Z)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to Z
    <except-pattern> (XX::'c\<^sub>a\<^sub>a BI) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YY \<w>\<i>\<t>\<h> PP @action to Z \<close>
  for Fa :: \<open>('p \<Rightarrow> ('c\<^sub>a, 'a\<^sub>a) \<phi>) \<Rightarrow> ('c,'a) \<phi>\<close> and Z :: \<open>('c\<^sub>a\<^sub>a, 'a\<^sub>a\<^sub>a) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def Except_Pattern_def
  using transformation\<^sub>\<Lambda>[unfolded \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [\<phi>reason_template default %To_ToA_derived_Tr_functor name Fa.to_traverse]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R mapper
\<Longrightarrow> (\<And>p. \<And>a \<in> D p x. a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> Z) \<close>
  unfolding Action_Tag_def \<r>Guard_def
  using transformation\<^sub>\<Lambda>[unfolded \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [\<phi>reason_template name Fa.\<A>simp [\<phi>transformation_based_simp default %\<phi>simp_derived_Tr_functor no trigger]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (\<forall>p. \<forall>a \<in> D p x. (a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b @action \<A>simp))
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>_transitive_simp \<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  using transformation\<^sub>\<Lambda>[unfolded atomize_Ball atomize_all Premise_def \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [\<phi>reason_template name Fa.\<A>backward_simp [\<phi>transformation_based_backward_simp default %\<phi>simp_derived_Tr_functor no trigger]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> (\<forall>p. \<forall>a \<in> D p x. (a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b @action \<A>backward_simp))
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x)
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fb U \<s>\<u>\<b>\<j> y. mapper g x y @action \<A>_backward_transitive_simp \<close>
  unfolding Action_Tag_def Premise_def \<r>Guard_def
  using transformation\<^sub>\<Lambda>[unfolded atomize_Ball atomize_all Premise_def \<r>Guard_def, where Fa=Fa and Fb=Fb and D=D and R=R and mapper=mapper] .

lemma [no_atp, \<phi>reason_template default %ToA_derived_one_to_one_functor name Fa.functional_transformation]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor\<^sub>\<Lambda> Fa Fb T U D R pred_mapper func_mapper
\<Longrightarrow> (\<And>p. \<And>a \<in> D p x. a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f p a \<Ztypecolon> U p \<w>\<i>\<t>\<h> P p a)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>p a. a \<in> D p x \<longrightarrow> f p a \<in> R p x) 
\<Longrightarrow> x \<Ztypecolon> Fa T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P x \<Ztypecolon> Fb U \<w>\<i>\<t>\<h> pred_mapper f P x \<close>
  unfolding \<r>Guard_def
  using apply_Functional_Transformation_Functor\<^sub>\<Lambda>[unfolded Argument_def,
            where func_mapper=func_mapper and pred_mapper=pred_mapper] .



subsection \<open>Separation Homomorphism\<close>

lemma Object_Sep_Homo\<^sub>I_subdom[
        \<phi>adding_property = false,
        \<phi>reason %\<phi>TA_varify_out except \<open>Object_Sep_Homo\<^sub>I _ ?var\<close>,
        \<phi>adding_property = true
      ]:
  \<open> Object_Sep_Homo\<^sub>I T Da
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Db \<subseteq> Da
\<Longrightarrow> Object_Sep_Homo\<^sub>I T Db\<close>
  unfolding Object_Sep_Homo\<^sub>I_def Premise_def subset_iff
  by blast

lemma [\<phi>reason_template default %\<phi>simp_derived_Tr_functor+5 name Fb.\<A>simp_sep_homo]:
  \<open> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>E Fa\<^sub>L Fa\<^sub>R Fb U\<^sub>L U\<^sub>R un
\<Longrightarrow> x \<Ztypecolon> Fb (U\<^sub>L \<^emph>\<^sub>\<A> U\<^sub>R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fa\<^sub>L U\<^sub>L \<^emph>\<^sub>\<A> Fa\<^sub>R U\<^sub>R \<s>\<u>\<b>\<j> y. y = un x @action \<A>simp\<close>
  unfolding Separation_Homo\<^sub>E_def Action_Tag_def Bubbling_def \<r>Guard_def
  by (clarsimp simp add: Subjection_transformation_rewr Ex_transformation_expn)

(*Object_Sep_Homo\<^sub>I is necessary at least for composition \<phi>-type
Object_Sep_Homo\<^sub>I B \<longleftrightarrow> Separation_Homo\<^sub>I ((\<Zcomp>) B) ((\<Zcomp>) B) ((\<Zcomp>) B) (\<lambda>x. x)
*)

(*There are two inner element \<open>a,b\<close>, we construct an inner transformation from \<open>(a \<Ztypecolon> T) * (b \<Ztypecolon> T)\<close>
    to \<open>(b * a) \<Ztypecolon> T\<close>
  Note here \<open>c = b * a\<close> only if the \<open>*\<close> is defined between b and a.
*)

lemma Separation_Homo_functor[\<phi>reason_template default %Object_Sep_Homo_functor]:
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

lemma [\<phi>reason_template name Fc.\<phi>Prod_ty []]:
  \<open> Separation_Homo\<^sub>I Ft Fu Fc T U UNIV (\<lambda>x. x)
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U (\<lambda>x. x)
\<Longrightarrow> Fc (T \<^emph> U) = Ft T \<^emph> Fu U \<close>
  unfolding Separation_Homo\<^sub>I_def Separation_Homo\<^sub>E_def
  by (rule \<phi>Type_eqI_Tr ; simp add: split_paired_all)

lemma [\<phi>reason_template name F\<^sub>T\<^sub>U.\<phi>Prod[]]:
  \<open> Separation_Homo\<^sub>I F\<^sub>T F\<^sub>U F\<^sub>T\<^sub>U T U D\<^sub>z f
\<Longrightarrow> Separation_Homo\<^sub>E F\<^sub>T F\<^sub>U F\<^sub>T\<^sub>U T U g
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> g (f x) = x \<and> x \<in> D\<^sub>z
\<Longrightarrow> (x \<Ztypecolon> F\<^sub>T T \<^emph> F\<^sub>U U) = (f x \<Ztypecolon> F\<^sub>T\<^sub>U (T \<^emph> U))\<close>
  unfolding Separation_Homo\<^sub>E_def Separation_Homo\<^sub>I_def Premise_def Transformation_def
            BI_eq_iff
  by (clarsimp; metis prod.collapse)

(* seemly useless
lemma [\<phi>reason_template name Fc.\<phi>Prod_Cond []]:
  \<open> Separation_Homo\<^sub>I_Cond Ft Fu Fc C T U UNIV (\<lambda>x. x)
\<Longrightarrow> Separation_Homo\<^sub>E_Cond Ft Fu Fc C T U UNIV (\<lambda>x. x)
\<Longrightarrow> Fc (T \<^emph>[C] U) = Ft T \<^emph>[C] Fu U \<close>
  unfolding Separation_Homo\<^sub>I_Cond_def Separation_Homo\<^sub>E_Cond_def
  by (rule \<phi>Type_eqI_Tr ; simp add: split_paired_all)
*)

lemma apply_conditioned_Separation_Functor_unzip:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U un)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Functional_Transformation_Functor Fc Ft (T \<^emph>[C] U) T D R pred_mapper func_mapper)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> D x \<and> \<not> C \<longrightarrow> fst a \<in> R x)
\<Longrightarrow> x \<Ztypecolon> Fc(T \<^emph>[C] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then un x else (func_mapper fst (\<lambda>_. True) x, unspec)) \<Ztypecolon> Ft(T) \<^emph>[C] Fu(U)\<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn'[symmetric] Premise_def
  apply (cases C; simp) 
  \<medium_left_bracket> premises FTF[] and [useful] and []
    note [[\<phi>trace_reasoning = 2]] 
    ;; apply_rule apply_Functional_Transformation_Functor[where f=\<open>fst\<close> and P=\<open>\<lambda>_. True\<close>, OF FTF]
    \<medium_left_bracket> \<medium_right_bracket>
  \<medium_right_bracket> .

(*TODO: a deriver controlling the form of \<open>Separation_Homo\<^sub>I_Cond\<close>
Here we give a quick but imperfect deriving without such control
note, also refer to the git branch Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond
*)

lemma [\<phi>reason_template default %\<phi>TA_derived_properties name Ft.Separation_Homo\<^sub>I_Cond]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>W \<Longrightarrow> Separation_Homo\<^sub>I Ft Fu F3 T U D z)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W \<Longrightarrow> Functional_Transformation_Functor Ft F3 T (T \<^emph>[C\<^sub>W] U) D' R' pred' func' )
\<Longrightarrow> Separation_Homo\<^sub>I_Cond Ft Fu F3 C\<^sub>W T U (?\<^sub>Z\<^sub>D[C\<^sub>W] D D' R') (?\<^sub>Z[C\<^sub>W] z (\<lambda>f. func' f (\<lambda>_. True))) \<close>
  unfolding Separation_Homo\<^sub>I_Cond_def Separation_Homo\<^sub>I_def Premise_def Action_Tag_def Simplify_def
            LPR_ctrl_def
  by (cases C\<^sub>W; clarsimp;
      insert apply_Functional_Transformation_Functor
                [unfolded Argument_def Premise_def,
                  where Fa=Ft and Fb=F3 and func_mapper=func' and f=\<open>(\<lambda>x. (x, unspec))\<close> and
                        pred_mapper=pred' and P=\<open>\<lambda>_. True\<close> and T=T and U=\<open>T \<^emph>[C\<^sub>W] U\<close> and
                        D=D' and R=R'];
      clarsimp;
      insert transformation_weaken; blast)

(*
lemma [\<phi>reason_template default %\<phi>TA_derived_properties name Ft.Separation_Homo\<^sub>I_Cond]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>W \<Longrightarrow> Separation_Homo\<^sub>I Ft Fu F3 T U D z)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W \<Longrightarrow> Functional_Transformation_Functor Ft F3 T (T \<^emph>[C\<^sub>W] U) D' (\<lambda>_. UNIV) pred' (\<lambda>f _. f) )
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] DD : ({x. LPR_ctrl C\<^sub>W \<longrightarrow> x \<in> D})) @action \<A>_template_reason unspec
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] ZZ : (\<lambda>x. if LPR_ctrl C\<^sub>W then z x else x)) @action \<A>_template_reason unspec
\<Longrightarrow> Separation_Homo\<^sub>I_Cond Ft Fu F3 C\<^sub>W T U DD ZZ \<close>
  unfolding Separation_Homo\<^sub>I_Cond_def Separation_Homo\<^sub>I_def Premise_def Action_Tag_def Simplify_def
            case_split_def
  apply (cases C\<^sub>W; clarsimp)
  subgoal for x y
    by (insert apply_Functional_Transformation_Functor
                [unfolded Argument_def Premise_def,
                  where Fa=Ft and Fb=F3 and func_mapper=\<open>\<lambda>f _. f\<close> and f=\<open>(\<lambda>x. (x, y))\<close> and
                        pred_mapper=pred' and P=\<open>\<lambda>_. True\<close> and T=T and U=\<open>T \<^emph>[C\<^sub>W] U\<close> and
                        D=D' and R=\<open>\<lambda>_. UNIV\<close>],
       clarsimp,
       insert transformation_weaken, blast) .
*)

lemma [\<phi>reason_template default %\<phi>TA_derived_properties name Ft.Separation_Homo\<^sub>E_Cond]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R \<Longrightarrow> Separation_Homo\<^sub>E Ft Fu F3 T U uz)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>R \<Longrightarrow> Functional_Transformation_Functor F3 Ft (T \<^emph>[C\<^sub>R] U) T D' R' pred' func' )
\<Longrightarrow> Separation_Homo\<^sub>E_Cond Ft Fu F3 C\<^sub>R T U (?\<^sub>U\<^sub>Z\<^sub>D[C\<^sub>R] D' R') (?\<^sub>U\<^sub>Z[C\<^sub>R] uz (\<lambda>f. func' f (\<lambda>_. True))) \<close>
  unfolding Separation_Homo\<^sub>E_Cond_def Separation_Homo\<^sub>E_def Premise_def Action_Tag_def Simplify_def
  by (cases C\<^sub>R; clarsimp;
      insert apply_Functional_Transformation_Functor[unfolded Argument_def Premise_def,
                  where Fa=F3 and Fb=Ft and func_mapper=func' and f=\<open>fst\<close> and
                        pred_mapper=pred' and P=\<open>\<lambda>_. True\<close> and U=T and T=\<open>T \<^emph>[C\<^sub>R] U\<close> and
                        D=D' and R=R'];
      clarsimp;
      metis (no_types, lifting) case_prodD transformation_weaken)

(*
lemma [\<phi>reason_template default %\<phi>TA_derived_properties name Ft.Separation_Homo\<^sub>E_Cond]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R \<Longrightarrow> Separation_Homo\<^sub>E Ft Fu F3 T U uz)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>R \<Longrightarrow> Functional_Transformation_Functor F3 Ft (T \<^emph>[C\<^sub>R] U) T D' R' pred' (\<lambda>f _. f) )
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] DD : {x. \<not> LPR_ctrl C\<^sub>R \<longrightarrow> (\<forall>(a,b) \<in> D' x. a \<in> R' x)}) @action \<A>_template_reason unspec
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] UZ : (\<lambda>x. if LPR_ctrl C\<^sub>R then uz x else x)) @action \<A>_template_reason unspec
\<Longrightarrow> Separation_Homo\<^sub>E_Cond Ft Fu F3 C\<^sub>R T U DD UZ \<close>
  unfolding Separation_Homo\<^sub>E_Cond_def Separation_Homo\<^sub>E_def Premise_def Action_Tag_def Simplify_def
  by ((cases C\<^sub>R; clarsimp),
      insert apply_Functional_Transformation_Functor[unfolded Argument_def Premise_def,
                  where Fa=F3 and Fb=Ft and func_mapper=\<open>\<lambda>f _. f\<close> and f=\<open>fst\<close> and
                        pred_mapper=pred' and P=\<open>\<lambda>_. True\<close> and U=T and T=\<open>T \<^emph>[C\<^sub>R] U\<close> and
                        D=D' and R=R'],
     clarsimp,
     metis (no_types, lifting) case_prod_conv transformation_weaken)
*)


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
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then uz (func_mapper f P x) else (func_mapper' fst (\<lambda>_. True) (func_mapper f P x), unspec)) \<Ztypecolon> F3 U \<^emph>[C] F2 R
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


subsubsection \<open>With Parameterization\<close>

lemma [\<phi>reason_template default %\<phi>simp_derived_Tr_functor+5 name Fb.\<A>simp_sep_homo]:
  \<open> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>\<Lambda>\<^sub>E Fa\<^sub>L Fa\<^sub>R Fb U\<^sub>L U\<^sub>R un
\<Longrightarrow> x \<Ztypecolon> Fb (\<lambda>p. U\<^sub>L p \<^emph>\<^sub>\<A> U\<^sub>R p) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fa\<^sub>L U\<^sub>L \<^emph>\<^sub>\<A> Fa\<^sub>R U\<^sub>R \<s>\<u>\<b>\<j> y. y = un x @action \<A>simp\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_def Action_Tag_def Bubbling_def \<r>Guard_def
  by (clarsimp simp add: Subjection_transformation_rewr Ex_transformation_expn)

lemma [\<phi>reason_template name Fc.\<phi>Prod_ty []]:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>I Ft Fu Fc T U UNIV (\<lambda>x. x)
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E Ft Fu Fc T U (\<lambda>x. x)
\<Longrightarrow> Fc (\<lambda>p. T p \<^emph> U p) = Ft T \<^emph> Fu U \<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_def Separation_Homo\<^sub>\<Lambda>\<^sub>E_def
  by (rule \<phi>Type_eqI_Tr ; simp add: split_paired_all)

lemma [\<phi>reason_template name F\<^sub>T\<^sub>U.\<phi>Prod[]]:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>I F\<^sub>T F\<^sub>U F\<^sub>T\<^sub>U T U D\<^sub>z f
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E F\<^sub>T F\<^sub>U F\<^sub>T\<^sub>U T U g
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> D\<^sub>z \<and> g (f x) = x
\<Longrightarrow> (x \<Ztypecolon> F\<^sub>T T \<^emph> F\<^sub>U U) = (f x \<Ztypecolon> F\<^sub>T\<^sub>U (\<lambda>p. T p \<^emph> U p))\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_def Separation_Homo\<^sub>\<Lambda>\<^sub>I_def Premise_def
            Transformation_def BI_eq_iff
  by (clarsimp; metis (no_types, lifting) prod.collapse)

(*
lemma [\<phi>reason_template name Fc.\<phi>Prod_Cond []]:
  \<open> Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond Ft Fu Fc C T U UNIV (\<lambda>x. x)
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond Ft Fu Fc C T U UNIV (\<lambda>x. x)
\<Longrightarrow> Fc (\<lambda>p. T p \<^emph>[C] U p) = Ft T \<^emph>[C] Fu U \<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond_def Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond_def
  by (rule \<phi>Type_eqI_Tr ; simp add: split_paired_all)
*)

declare [[\<phi>trace_reasoning = 2]]

lemma apply_conditioned_Separation_Functor\<^sub>\<Lambda>_unzip:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E Ft Fu Fc T U un)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> Fc Ft (\<lambda>p. T p \<^emph>[C] U p) T D R pred_mapper func_mapper)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>p a. a \<in> D p x \<and> \<not> C \<longrightarrow> fst a \<in> R p x)
\<Longrightarrow> x \<Ztypecolon> Fc(\<lambda>p. T p \<^emph>[C] U p) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then un x else (func_mapper (\<lambda>_. fst) (\<lambda>_ _. True) x, unspec)) \<Ztypecolon> Ft(T) \<^emph>[C] Fu(U)\<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_def \<phi>Prod_expn'[symmetric] Premise_def
  apply (cases C; simp)
  \<medium_left_bracket> premises FTF[] and [useful] and [] 
    apply_rule apply_Functional_Transformation_Functor\<^sub>\<Lambda>[where f=\<open>\<lambda>_. fst\<close> and P=\<open>\<lambda>_ _. True\<close>, OF FTF]
    \<medium_left_bracket> \<medium_right_bracket>
  \<medium_right_bracket> .


lemma [\<phi>reason_template default %\<phi>TA_derived_properties name Ft.Separation_Homo\<^sub>I_Cond]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>W \<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>I Ft Fu F3 T U D z)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>W \<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> Ft F3 T (\<lambda>p. T p \<^emph>[C\<^sub>W] U p) D' R' pred' func' )
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] DD : (if LPR_ctrl C\<^sub>W then D else {x. \<forall>p a. a \<in> D' p (fst x) \<longrightarrow> (a, unspec) \<in> R' p (fst x)})) @action \<A>_template_reason undefined
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] ZZ : (if LPR_ctrl C\<^sub>W then z else func' (\<lambda>_ x. (x, unspec)) (\<lambda>_ _. True) o fst)) @action \<A>_template_reason undefined
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond Ft Fu F3 C\<^sub>W T U DD ZZ \<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond_def Separation_Homo\<^sub>\<Lambda>\<^sub>I_def Premise_def Action_Tag_def Simplify_def
            LPR_ctrl_def
  by (cases C\<^sub>W; clarsimp;
      insert apply_Functional_Transformation_Functor\<^sub>\<Lambda>
                [unfolded Argument_def Premise_def,
                  where Fa=Ft and Fb=F3 and func_mapper=func' and f=\<open>\<lambda>_ x. (x, unspec)\<close> and
                        pred_mapper=pred' and P=\<open>\<lambda>_ _. True\<close> and T=T and U=\<open>\<lambda>p. T p \<^emph>[C\<^sub>W] U p\<close> and
                        D=D' and R=R'];
      clarsimp;
      insert transformation_weaken; blast)

lemma [\<phi>reason_template default %\<phi>TA_derived_properties name Ft.Separation_Homo\<^sub>E_Cond]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C\<^sub>R \<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E Ft Fu F3 T U uz)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C\<^sub>R \<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> F3 Ft (\<lambda>p. T p \<^emph>[C\<^sub>R] U p) T D' R' pred' func' )
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] DD : (if LPR_ctrl C\<^sub>R then UNIV else {x. \<forall>p. \<forall>(a,b) \<in> D' p x. a \<in> R' p x})) @action \<A>_template_reason undefined
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>instantiation] UZ : (if LPR_ctrl C\<^sub>R then uz else (\<lambda>x. (func' (\<lambda>_. fst) (\<lambda>_ _. True) x, unspec)))) @action \<A>_template_reason undefined
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond Ft Fu F3 C\<^sub>R T U DD UZ \<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond_def Separation_Homo\<^sub>\<Lambda>\<^sub>E_def Premise_def Action_Tag_def Simplify_def
  by (cases C\<^sub>R; clarsimp;
      insert apply_Functional_Transformation_Functor\<^sub>\<Lambda>[unfolded Argument_def Premise_def,
                  where Fa=F3 and Fb=Ft and func_mapper=func' and f=\<open>\<lambda>_. fst\<close> and
                        pred_mapper=pred' and P=\<open>\<lambda>_ _. True\<close> and U=T and T=\<open>\<lambda>p. T p \<^emph>[C\<^sub>R] U p\<close> and
                        D=D' and R=R'];
      clarsimp;
      metis (no_types, lifting) case_prodD transformation_weaken)



subsection \<open>Semimodule\<close>

subsubsection \<open>Zero\<close>

lemma [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice,
       \<phi>adding_property = true]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> Semimodule_Zero F zero \<close>
  unfolding Closed_Semimodule_Zero_def Semimodule_Zero_def
  by simp

paragraph \<open>Equations\<close>

lemma [\<phi>reason_template name F.scalar_zero [assertion_simps, simp]]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> (x \<Ztypecolon> F zero) = 1 \<close>
  unfolding Closed_Semimodule_Zero_def by blast

lemma [\<phi>reason_template name F.scalar_zero' [assertion_simps, simp]]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason None
\<Longrightarrow> (x \<Ztypecolon> F zero') = 1 \<close>
  unfolding Closed_Semimodule_Zero_def Simplify_def Action_Tag_def
  by blast

paragraph \<open>Identity Elements\<close>

lemma [\<phi>reason_template default %derived_identity_element+5]:
  \<open> \<g>\<u>\<a>\<r>\<d> Closed_Semimodule_Zero F zero
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> zero' = zero
\<Longrightarrow> Identity_Elements\<^sub>E (F zero') (\<lambda>_. True) \<close>
  unfolding Identity_Elements\<^sub>E_def Identity_Element\<^sub>E_def \<r>Guard_def
            Transformation_def Premise_def Closed_Semimodule_Zero_def
  by clarsimp

lemma [\<phi>reason_template default %derived_identity_element+5]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_Zero F zero
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> zero' = zero
\<Longrightarrow> Identity_Elements\<^sub>I (F zero') (\<lambda>_. True) (\<lambda>_. True) \<close>
  unfolding Identity_Elements\<^sub>I_def Identity_Element\<^sub>I_def \<r>Guard_def
            Transformation_def Premise_def Semimodule_Zero_def
  by clarsimp


paragraph \<open>Transformations\<close>

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Zero F zero
\<Longrightarrow> NO_SIMP (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F zero \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def NO_SIMP_def
  using mk_elim_transformation by blast

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Zero F zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason None
\<Longrightarrow> NO_SIMP (1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F zero' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def NO_SIMP_def Simplify_def Action_Tag_def
  using mk_elim_transformation by blast

lemma [\<phi>reason_template default %ToA_derived_red ]:
  \<open> Semimodule_Zero F zero
\<Longrightarrow> NO_SIMP (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F zero) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Semimodule_Zero_def NO_SIMP_def
  using transformation_bi_frame
  by fastforce

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Zero F zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason None
\<Longrightarrow> NO_SIMP (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> F zero') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Semimodule_Zero_def NO_SIMP_def Simplify_def Action_Tag_def
  using transformation_bi_frame
  by fastforce

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Zero F zero
\<Longrightarrow> NO_SIMP (((), snd x) \<Ztypecolon> F zero \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F zero \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def NO_SIMP_def
  by (cases x; cases C; clarsimp)

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Semimodule_Zero F zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason None
\<Longrightarrow> NO_SIMP (((), snd x) \<Ztypecolon> F zero \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> F zero' \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y) \<close>
  unfolding Semimodule_Zero_def NO_SIMP_def Simplify_def Action_Tag_def
  by (cases x; cases C; clarsimp)

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F zero \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason None
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F zero' \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def Simplify_def Action_Tag_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F zero \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason None
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F zero' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  for R :: \<open>'c::sep_magma_1 set\<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def Simplify_def Action_Tag_def
  by simp

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (any, snd x) \<Ztypecolon> F zero \<^emph>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def
  by (cases C; clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> Closed_Semimodule_Zero F zero
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> zero' : zero) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH zero zero' @action \<A>_template_reason None
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (any, snd x) \<Ztypecolon> F zero' \<^emph>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Closed_Semimodule_Zero_def Identity_Element\<^sub>I_def NO_SIMP_def Simplify_def Action_Tag_def
  by (cases C; clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn')



subsubsection \<open>One\<close>

paragraph \<open>Rewrites Eliminating Identity Scalar\<close>

lemma [\<phi>reason_template name F.scalar_one_ty [assertion_simps, simp]]:
  \<open> Semimodule_One\<^sub>I F T\<^sub>1 one (\<lambda>_. True) (\<lambda>x. x) P\<^sub>I
\<Longrightarrow> Semimodule_One\<^sub>E F T\<^sub>1 one (\<lambda>_. True) (\<lambda>x. x) P\<^sub>E
\<Longrightarrow> F one = T\<^sub>1 \<close>
  unfolding Semimodule_One\<^sub>I_def Semimodule_One\<^sub>E_def
  by (rule \<phi>Type_eqI_Tr; clarsimp simp add: Transformation_def)

lemma [\<phi>reason_template name F.scalar_one_ty' [assertion_simps, simp]]:
  \<open> Semimodule_One\<^sub>I F T\<^sub>1 one (\<lambda>_. True) (\<lambda>x. x) P\<^sub>I
\<Longrightarrow> Semimodule_One\<^sub>E F T\<^sub>1 one (\<lambda>_. True) (\<lambda>x. x) P\<^sub>E
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason None
\<Longrightarrow> F one' = T\<^sub>1 \<close>
  unfolding Semimodule_One\<^sub>I_def Semimodule_One\<^sub>E_def Simplify_def Action_Tag_def
  by (rule \<phi>Type_eqI_Tr; clarsimp simp add: Transformation_def)

lemma [\<phi>reason_template name F.scalar_one [assertion_simps, simp]]:
  \<open> Semimodule_One\<^sub>I F T\<^sub>1 one D\<^sub>I f P\<^sub>I
\<Longrightarrow> Semimodule_One\<^sub>E F T\<^sub>1 one D\<^sub>E g P\<^sub>E
\<Longrightarrow> Object_Equiv (F one) eq @action \<A>_template_reason undefined
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D\<^sub>E x \<and> D\<^sub>I (g x) \<and> eq (f (g x)) x
\<Longrightarrow> (x \<Ztypecolon> F one) = (g x \<Ztypecolon> T\<^sub>1) \<close>
  unfolding Semimodule_One\<^sub>I_def Semimodule_One\<^sub>E_def BI_eq_iff Transformation_def Premise_def
            Object_Equiv_def Action_Tag_def
  by (clarsimp; metis)

lemma [\<phi>reason_template name F.scalar_one' [assertion_simps, simp]]:
  \<open> Semimodule_One\<^sub>I F T\<^sub>1 one D\<^sub>I f P\<^sub>I
\<Longrightarrow> Semimodule_One\<^sub>E F T\<^sub>1 one D\<^sub>E g P\<^sub>E
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason None
\<Longrightarrow> Object_Equiv (F one) eq @action \<A>_template_reason undefined
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D\<^sub>E x \<and> D\<^sub>I (g x) \<and> eq (f (g x)) x
\<Longrightarrow> (x \<Ztypecolon> F one') = (g x \<Ztypecolon> T\<^sub>1) \<close>
  unfolding Semimodule_One\<^sub>I_def Semimodule_One\<^sub>E_def BI_eq_iff Transformation_def Premise_def
            Simplify_def Action_Tag_def Object_Equiv_def
  by (clarsimp; metis)


paragraph \<open>Protector Preventing Eliminating the just Introduced Scalar Identity\<close>

definition [iff, \<phi>safe_simp]: \<open>introduced X \<equiv> X\<close>

subparagraph \<open>arith_eval\<close>

lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>equation\<^sub>2\<^sub>1 (introduced _) _ _\<close>]:
  \<open> equation\<^sub>2\<^sub>1 a b X
\<Longrightarrow> equation\<^sub>2\<^sub>1 (introduced a) b X \<close>
  by simp

lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>equation\<^sub>2\<^sub>1 _ (introduced _) _\<close>]:
  \<open> equation\<^sub>2\<^sub>1 a b X
\<Longrightarrow> equation\<^sub>2\<^sub>1 a (introduced b) X \<close>
  by simp

lemma [\<phi>reason %\<A>_partial_add_normalizing for \<open>equation\<^sub>2\<^sub>1 _ _ (introduced _)\<close>]:
  \<open> equation\<^sub>2\<^sub>1 a b X
\<Longrightarrow> equation\<^sub>2\<^sub>1 a b (introduced X) \<close>
  by simp

lemma [\<phi>reason %\<A>_partial_add_normalizing]:
  \<open> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c a b ab c X
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c a (introduced b) ab c X \<close>
  by simp

lemma [\<phi>reason %\<A>_partial_add_normalizing]:
  \<open> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c a b ab c X
\<Longrightarrow> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c a b ab c (introduced X) \<close>
  by simp

lemma [\<phi>reason %\<A>_partial_add_normalizing]:
  \<open> equation\<^sub>3\<^sub>1 a b c X
\<Longrightarrow> equation\<^sub>3\<^sub>1 a (introduced b) c X \<close>
  by simp

lemma [\<phi>reason %\<A>_partial_add_normalizing]:
  \<open> equation\<^sub>3\<^sub>1 a b c X
\<Longrightarrow> equation\<^sub>3\<^sub>1 a b c (introduced X) \<close>
  by simp

lemma [\<phi>reason %partial_add_overlaps_norm]:
  \<open> partial_add_overlaps a b
\<Longrightarrow> partial_add_overlaps (introduced a) b \<close>
  by simp

lemma [\<phi>reason %partial_add_overlaps_norm]:
  \<open> partial_add_overlaps a b
\<Longrightarrow> partial_add_overlaps a (introduced b) \<close>
  by simp


paragraph \<open>ToA Eliminating Identity Scalar\<close>

subparagraph \<open>Implementation\<close>

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D\<^sub>E g P\<^sub>E
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] one'' : one'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> is_id_element one (NO_SIMP one'')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D\<^sub>E x
\<Longrightarrow> NO_SIMP (g x \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> x \<Ztypecolon> F one' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<and> P\<^sub>E x
      <except-pattern> x \<Ztypecolon> F (introduced one') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YYY \<w>\<i>\<t>\<h> PPP \<close>
  unfolding Semimodule_One\<^sub>I_def Semimodule_One\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def
            Transformation_def Except_Pattern_def is_id_element_def Simplify_def
  by (clarsimp; metis)

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D\<^sub>E g P\<^sub>E
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] one'' : one'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> is_id_element one (NO_SIMP one'')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D\<^sub>E x
\<Longrightarrow> NO_SIMP (R * (g x \<Ztypecolon> T\<^sub>1) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> R * (x \<Ztypecolon> F one') \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<and> P\<^sub>E x
      <except-pattern> RRR * (x \<Ztypecolon> F (introduced one')) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YYY \<w>\<i>\<t>\<h> PPP \<close>
  unfolding Semimodule_One\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Transformation_def
            Except_Pattern_def is_id_element_def Simplify_def
  by (clarsimp; metis)
  \<comment> \<open>the rule is invoked only once for each \<phi>-type in the source, so no problem to invoke the
      simple tactic for each time.\<close>

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D g P\<^sub>E
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst x)
\<Longrightarrow> NO_SIMP (apfst g x \<Ztypecolon> T\<^sub>1 \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> x \<Ztypecolon> F one \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<and> P\<^sub>E (fst x) \<close>
  unfolding Semimodule_One\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Transformation_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn'; metis)

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D g P\<^sub>E
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason None
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst x)
\<Longrightarrow> NO_SIMP (apfst g x \<Ztypecolon> T\<^sub>1 \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> x \<Ztypecolon> F one' \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<and> P\<^sub>E (fst x) \<close>
  unfolding Semimodule_One\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Simplify_def Action_Tag_def
            Transformation_def Except_Pattern_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn'; metis)

lemma [\<phi>reason_template default %derived_SE_red_scalar_one]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D g P\<^sub>E
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] one'' : one'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> is_id_element one (NO_SIMP one'')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst x)
\<Longrightarrow> NO_SIMP (apfst g x \<Ztypecolon> T\<^sub>1 \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> x \<Ztypecolon> F one' \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<and> P\<^sub>E (fst x)
      <except-pattern> x \<Ztypecolon> F (introduced one') \<^emph>[CCC] WWW \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YYY \<w>\<i>\<t>\<h> PPP \<close>
  unfolding Semimodule_One\<^sub>E_def NO_SIMP_def \<r>Guard_def Premise_def Transformation_def
            Except_Pattern_def Simplify_def is_id_element_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn'; metis)



lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] one'' : one'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> is_id_element one (NO_SIMP one'')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<^sub>1 \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F one' \<w>\<i>\<t>\<h> P \<and> P\<^sub>I x
      <with-pattern> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> var \<Ztypecolon> F one' \<w>\<i>\<t>\<h> PP
      <except-pattern> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x'' \<Ztypecolon> F (introduced one') \<w>\<i>\<t>\<h> PP \<close>
  unfolding Semimodule_One\<^sub>I_def NO_SIMP_def \<r>Guard_def Premise_def Except_Pattern_def
            Transformation_def With_Pattern_def Simplify_def is_id_element_def
  by (simp; metis)

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] one'' : one'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> is_id_element one (NO_SIMP one'')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<^sub>1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F one' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<and> P\<^sub>I x
      <with-pattern> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> var \<Ztypecolon> F one' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> PP
      <except-pattern> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x'' \<Ztypecolon> F (introduced one') \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> PP \<close>
  unfolding Semimodule_One\<^sub>I_def NO_SIMP_def \<r>Guard_def Premise_def Transformation_def
            With_Pattern_def Except_Pattern_def is_id_element_def Simplify_def
  by (cases C; clarsimp; metis)

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst x)
\<Longrightarrow> NO_MATCH (id one'') one @action \<A>_template_reason undefined
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<^sub>1 \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst f x \<Ztypecolon> F one \<^emph>[C] R \<w>\<i>\<t>\<h> P \<and> P\<^sub>I (fst x)
      <with-pattern> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> var \<Ztypecolon> F one \<^emph>[CC] RR \<w>\<i>\<t>\<h> PP \<close>
  unfolding Semimodule_One\<^sub>I_def NO_SIMP_def \<r>Guard_def Premise_def Transformation_def With_Pattern_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn'; metis)

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I
\<Longrightarrow> (\<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> one' : one) @action \<A>_template_reason undefined
\<Longrightarrow> NO_MATCH one one' @action \<A>_template_reason None
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst x)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<^sub>1 \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst f x \<Ztypecolon> F one' \<^emph>[C] R \<w>\<i>\<t>\<h> P \<and> P\<^sub>I (fst x)
      <with-pattern> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> var \<Ztypecolon> F one' \<^emph>[CC] RR \<w>\<i>\<t>\<h> PP \<close>
  unfolding Semimodule_One\<^sub>I_def NO_SIMP_def \<r>Guard_def Premise_def Simplify_def Action_Tag_def
            Transformation_def With_Pattern_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn'; metis)

lemma [\<phi>reason_template default %derived_SE_red_scalar_one]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<s>\<a>\<f>\<e>] one'' : one'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> is_id_element one (NO_SIMP one'')
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst x)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T\<^sub>1 \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst f x \<Ztypecolon> F one' \<^emph>[C] R \<w>\<i>\<t>\<h> P \<and> P\<^sub>I (fst x)
      <with-pattern> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> var \<Ztypecolon> F one' \<^emph>[CC] RR \<w>\<i>\<t>\<h> PP
      <except-pattern> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x'' \<Ztypecolon> F (introduced one') \<^emph>[CC] RR \<w>\<i>\<t>\<h> PP \<close>
  unfolding Semimodule_One\<^sub>I_def NO_SIMP_def \<r>Guard_def Premise_def Transformation_def
            With_Pattern_def Except_Pattern_def Simplify_def is_id_element_def
  by (cases x; cases C; clarsimp simp add: \<phi>Prod_expn'; metis)



paragraph \<open>Reasoning when having SDistr\<close>

text \<open>The difficulty of reasoning \<phi>-type transformations lies in the two directions that 
  the transformations can follow, hierarchically swapping an inner \<phi>-type out \<open>F (G T) \<longrightarrow> G (F T)\<close>
  and horizontally over \<open>*\<close> including splitting and merging.

  As an example example, the reasoning of transformation
  \<open>x \<Ztypecolon> F a T * others \<longrightarrow> y \<Ztypecolon> F b U\<close> with \<open>a \<le> b\<close> can reduce to 2 subgoals, \<open>T \<longrightarrow> F (b/a) U\<close> which looks
  for the missed portion from the inner hierarchy of \<open>T\<close>, or \<open>others \<longrightarrow> F (b-a) U\<close> which looks
  horizontally from the \<phi>-types beside, or even any mixture of the two subgoals -- some portion from inner
  and some portion beside.

  To reduce the search space, we first normalize an assertion by swapping commutative \<phi>-type operators
  to move identical operators into the same level, so that the later reasoning only needs to consider
  horizontal splitting and merging. To do so, we assign a weight to each \<phi>-type such that two \<phi>-types
  are of an identical weight iff they are identical.
  \<phi>-Types of a higher weight will sink towards the leaves during the normalization,
  so the normalization ensures \<open>weight(F) \<le> weight(G)\<close> for any normalized term \<open>F (G T)\<close> iff \<open>F\<close>
  is commutative over \<open>G\<close> and \<open>F,G\<close> have a weight.
  The weight can be annotated by users, to have a better control of the normalization,
  or simplify by lexical order if not significant.

  When identical \<phi>-types are on the same level, the reasoning of the transformations
  \<open>x \<Ztypecolon> F a T \<longrightarrow> y \<Ztypecolon> U\<close> or \<open>y \<Ztypecolon> U \<longrightarrow> x \<Ztypecolon> F a T\<close> where a semimodule \<phi>-type is given in one side but
  missed in the opposite side, can decide whether to embed the opposite \<phi>-type
  \<open>U\<close> into a semimodule \<open>F 1 U\<close> of identity scalar, by checking whether the weight of \<open>U\<close> is greater than
  the weight of \<open>F a T\<close>, which implies no swappable semimodule \<open>F\<close> that can move here can be seen in \<open>U\<close>.

  If we denote \<open>F > G \<triangleq> weight(F) > weight(G) \<and> commutative(F,G)\<close>, the normalization ensures in
  a given syntactic tree of \<phi>-type operators, any path from the root to a leaf \<phi>-type is non-descending,
  i.e., \<open>\<not> (F > G)\<close> for any adjacent \<open>F, G\<close>, i.e., \<open>F\<close> is not heavier than \<open>G\<close> if \<open>commutative(F,G)\<close>.
  A problem is whether all syntactic tree of \<phi>-type operators can be uniquely normalized.
  *: The check of \<open>F > G\<close> is carried by LP reasoner \<open>Require_Weight_Norm\<close> in the code.

  For the sake of unique normalization, we require all commutativity between the \<phi>-type operators is transitive.
  We designate \<open>commutative(F,G)\<close> to mean \<open>F\<close> can be swapped into \<open>G\<close>, \<open>\<exists>f. x \<Ztypecolon> F (G T) \<longrightarrow> f(x) \<Ztypecolon> G (F T)\<close>,
  but not necessarily reversely.
  The transitivity means \<open>commutative(F\<^sub>1,F\<^sub>2) \<and> commutative(F\<^sub>2,F\<^sub>3) \<longrightarrow> commutative(F\<^sub>1,F\<^sub>3)\<close>.
  If we draw a directed edge from \<open>F\<close> to \<open>G\<close> to mean \<open>weight(F) < weight(G)\<close> and \<open>F\<close> can be swapped with \<open>G\<close>
  by any steps of swapping adjacent operators in the sequence (another name of the path).
  The transitivity ensures any given sequence generates a disjoint union of several fully connected
  directed acyclic graph.
  Therefore, for any given sequence, we only need to swap any occurrences of \<open>F, G\<close> where \<open>F > G\<close> (a bubbling sort),
  and any order of swapping results in the unique normalized form, which is the topological sorting
  of the generated graph with connected components in the order of their occurrences in the sequence.
  Therefore, a path can be uniquely normalized.

  Another issue is many paths exist in the tree. We can normalize the paths one by one in any order.
  An operator \<open>F\<close> can be of multi-arity, so multiple children. Assume one path of the operand \<open>G\<^sub>i\<close> is
  normalized, when the normalization of another operand \<open>G\<^sub>j\<close> swaps \<open>G\<^sub>j\<close> out of \<open>F\<close>, \<open>G\<^sub>j\<close> is inserted
  into the normalized path of \<open>G\<^sub>i\<close>, changing it from \<open>Root \<dots> F G\<^sub>i \<dots> Leaf\<close> to \<open>Root \<dots> G\<^sub>j F G\<^sub>i \<dots> Leaf\<close>.
  The sub-sequence \<open>G\<^sub>i \<dots> Leaf\<close> is unchanged but the property of \<open>Root \<dots> G\<^sub>j F\<close> is temporarily broken.
  However, with the normalization of the path \<open>G\<^sub>j\<close>, \<open>Root \<dots> G\<^sub>j F\<close> will be normalized, and the concatenation
  of the normalized \<open>Root \<dots> G\<^sub>j F\<close> with \<open>G\<^sub>i \<dots> Leaf\<close> also yields a normalized path, because \<open>\<not> (G\<^sub>i > F)\<close>.

  Besides, not all multi-arity operator pair \<open>(F,G)\<close> has partial commutativity (in sense of fixing
  all of its operands except one, \<open>F (fixed, G(T)) \<longrightarrow> G (F (fixed, T))\<close>, so reducing the notion of
  multi-arity commutativity to the normal commutativity of single-arity type operators),
  but total commutativity where all operands are of the same \<phi>-type and swapped together,
  e.g., \<open>F (G(T), G(U)) \<longrightarrow> G (F (T, U))\<close> and \<open>F=(\<^emph>), G=((\<^bold>\<rightarrow>) k)\<close> is an instance.
  It brings no problem to the normalization, because it is swapping \<open>F\<close> and \<open>G\<close> simultaneously in
  the paths of all its operands, and this swapping is valid in either of the paths in our bubbling sort
  algorithm.

  At last, not all operators need normalization. Operators like \<open>\<^emph>, +, \<and>, \<Sigma>\<close> are already handled well
  by the reasoner, so they can occur anywhere in the tree and there is no need to move them onto certain same level.
  We do not assign a weight to them so they do not have any weight relation with others.
  It optimizes the normalization performance.
\<close>

subparagraph \<open>Preliminary\<close>

consts restore_from_semimodule :: \<open>bool \<Rightarrow> ('s \<Rightarrow> ('e, 'd) \<phi>) \<Rightarrow> action\<close> 

declare [[ \<phi>reason_default_pattern
     \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _ @action restore_from_semimodule True ?F\<close> \<Rightarrow>
     \<open>_ \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<w>\<i>\<t>\<h> _ @action restore_from_semimodule True ?F\<close>     (100)
 and \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _ @action restore_from_semimodule False ?F\<close> \<Rightarrow>
     \<open>_ \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _ @action restore_from_semimodule False ?F\<close>    (100)
]]

\<phi>reasoner_group restore_from_semimodule = (1000, [1000,1001]) for \<open>_ @action restore_from_semimodule _ _\<close>
  \<open>The reasoning later lifts a \<phi>-type in to a semimodule with scalar one. The lifted semimodule
   not always succeeds, and may return with no change. If so, the reasoning process here, restore the
   lifted semimodule back to the original \<phi>-type, by unwrapping the scalar one. \<close>

lemma [\<phi>reason %restore_from_semimodule+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F (introduced one) @action restore_from_semimodule True F \<close>
  unfolding Semimodule_One\<^sub>I_def Action_Tag_def Transformation_def Premise_def \<r>Guard_def
  by simp

lemma [\<phi>reason %restore_from_semimodule+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D f P\<^sub>E
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F (introduced one) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T\<^sub>1 @action restore_from_semimodule False F \<close>
  unfolding Semimodule_One\<^sub>E_def Action_Tag_def Transformation_def Premise_def \<r>Guard_def
  by simp

lemma [\<phi>reason %restore_from_semimodule for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ @action restore_from_semimodule _ _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action restore_from_semimodule Any F \<close>
  unfolding Action_Tag_def
  by simp


subparagraph \<open>Main\<close>

(*
lemma [\<phi>reason_template default %derived_SE_inj_to_module name F.wrap_module_src\<^sub>1]:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps one b
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_Swap_Norm (F one)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F F'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I
\<Longrightarrow> NO_SIMP (f x \<Ztypecolon> F (introduced one) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' b \<w>\<i>\<t>\<h> P)
      \<comment> \<open>the \<open>introduced\<close> here protects the lifted semimodule from being reduced immediately\<close>
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' b \<w>\<i>\<t>\<h> P \<and> P\<^sub>I x
      <except-pattern> xx \<Ztypecolon> F aa \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' b \<w>\<i>\<t>\<h> PP \<close>
  unfolding Semimodule_One\<^sub>I_def Transformation_def Premise_def \<r>Guard_def NO_SIMP_def
            Except_Pattern_def
  by simp blast
*)

lemma [\<phi>reason_template default %derived_SE_inj_to_module name F.wrap_module_src]:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps one b
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (F one) True
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F F'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I
\<Longrightarrow> NO_SIMP ((f (fst x), w) \<Ztypecolon> F (introduced one) \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' b \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (
    if C then (snd x \<Ztypecolon> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W  @action restore_from_semimodule True F)
         else (w, W') = (snd x, W))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst x)
\<Longrightarrow> x \<Ztypecolon> T\<^sub>1 \<^emph>[C] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' b \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P
      <except-pattern> xx \<Ztypecolon> F aa \<^emph>[C] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' b \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P \<close>
  unfolding Semimodule_One\<^sub>I_def Transformation_def Premise_def \<r>Guard_def
            Action_Tag_def NO_SIMP_def Except_Pattern_def
  by (cases C; cases C\<^sub>R; clarsimp; metis)

(*
lemma [\<phi>reason_template default %derived_SE_inj_to_module name F.wrap_module_tgt\<^sub>1]:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps a one
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_Swap_Norm (F one)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' F
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D f P\<^sub>E
\<Longrightarrow> NO_SIMP (y \<Ztypecolon> F' a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F (introduced one) \<w>\<i>\<t>\<h> P)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> y \<Ztypecolon> F' a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T\<^sub>1 \<w>\<i>\<t>\<h> P \<and> P\<^sub>E x
      <except-pattern> y \<Ztypecolon> F' a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xx \<Ztypecolon> F bb \<w>\<i>\<t>\<h> PP \<close>
  unfolding Semimodule_One\<^sub>E_def Transformation_def Premise_def \<r>Guard_def NO_SIMP_def
            Except_Pattern_def
  by simp blast
*)

lemma [\<phi>reason_template default %derived_SE_inj_to_module+1 name F.wrap_module_tgt]:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps a one
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (F one) False
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' F
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D f P\<^sub>E
\<Longrightarrow> NO_SIMP (y \<Ztypecolon> F' a \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> F (introduced one) \<^emph>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (
    if C then (snd x \<Ztypecolon> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> r \<Ztypecolon> R' @action restore_from_semimodule False F)
         else (r, R') = (r, R))
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (fst x)
\<Longrightarrow> y \<Ztypecolon> F' a \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (f (fst x), r) \<Ztypecolon> T\<^sub>1 \<^emph>[C] R' \<w>\<i>\<t>\<h> P
      <except-pattern> y \<Ztypecolon> F' a \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> xx \<Ztypecolon> F bb \<^emph>[C] R' \<w>\<i>\<t>\<h> P \<close>
  unfolding Semimodule_One\<^sub>E_def Transformation_def Premise_def \<r>Guard_def
            Action_Tag_def NO_SIMP_def Except_Pattern_def
  by (cases C; cases C\<^sub>W; clarsimp; blast)

declare [[\<phi>trace_reasoning = 2]]

lemma ToA_mapper_MOne_src
  [no_atp, \<phi>reason_template default %\<phi>mapToA_derived_module_wrapper name F.mapper_wrap_module_src]:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps a one
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps b one'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (F one) True
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (F one') True
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' F
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' G
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' G'

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D\<^sub>I I\<^sub>1 P\<^sub>I
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E G U\<^sub>1 one' D\<^sub>E E\<^sub>1 P\<^sub>E

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>fst ` D. D\<^sub>I x \<and> D\<^sub>E (f (I\<^sub>1 x)))

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F' a \<^emph>[C\<^sub>R] R \<mapsto> G' b \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F (introduced one) \<^emph>[C\<^sub>W] W \<mapsto> G (introduced one') \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> apfst I\<^sub>1 ` D

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F' a \<^emph>[C\<^sub>R] R \<mapsto> G' b \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> (E\<^sub>1 o f o I\<^sub>1) \<otimes>\<^sub>f w : T\<^sub>1 \<^emph>[C\<^sub>W] W \<mapsto> U\<^sub>1 \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h o apfst I\<^sub>1 \<s>\<e>\<t>\<t>\<e>\<r> apfst E\<^sub>1 o s \<i>\<n> D \<close>
  unfolding \<r>Guard_def
  including prevent_eliminate_IE_\<phi>Cond_Unital
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
\<medium_left_bracket> premises _ and _ and _ and _ and _ and _ and _ and S1I[] and S1E[] and _ and Tr[]

  apply_rule apply_Semimodule_One\<^sub>I[OF S1I, THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans]]
  apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>apfst I\<^sub>1 x\<close>]
\<medium_right_bracket> apply(rule conjunctionI, rule)
\<medium_left_bracket> premises _ and _ and _ and _ and _ and _ and _ and S1I[] and S1E[] and _ and Tr[]
  apply_rule ToA_Mapper_backward[OF Tr]
    certified by (of_tac x, auto_sledgehammer) ;;
  apply_rule apply_Semimodule_One\<^sub>E[OF S1E, THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans]]
    certified by (insert ToA_Mapper_f_expn[OF Tr], auto_sledgehammer) ;;

\<medium_right_bracket> by (rule conjunctionI, rule, drule ToA_Mapper_f_expn_rev, clarsimp)


(*
lemma ToA_mapper_MOne_src
  [no_atp, \<phi>reason_template default %derived_SE_inj_to_module name F.mapper_wrap_module_src]:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps a one
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (F one) True
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' F

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F T\<^sub>1 one D\<^sub>1 I\<^sub>1 P\<^sub>E

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>fst ` D. D\<^sub>1 x)

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F' a \<^emph>[C\<^sub>R] R \<mapsto> U \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F (introduced one) \<^emph>[C\<^sub>W] W \<mapsto> U' \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> apfst I\<^sub>1 ` D

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F' a \<^emph>[C\<^sub>R] R \<mapsto> U \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> (f o I\<^sub>1) \<otimes>\<^sub>f w : T\<^sub>1 \<^emph>[C\<^sub>W] W \<mapsto> U' \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h o apfst I\<^sub>1 \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D \<close>
  unfolding \<r>Guard_def
  including prevent_eliminate_IE_\<phi>Cond_Unital
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
\<medium_left_bracket> premises _ and _ and _ and  S1I[] and _ and Tr[]

  apply_rule apply_Semimodule_One\<^sub>I[OF S1I, THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans]]
  apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>apfst I\<^sub>1 x\<close>]
\<medium_right_bracket> apply(rule conjunctionI, rule)
\<medium_left_bracket> premises _ and _ and _ and S1I[] and _ and Tr[]
  apply_rule ToA_Mapper_backward[OF Tr]
\<medium_right_bracket> by(rule conjunctionI, rule, drule ToA_Mapper_f_expn_rev, clarsimp)
*)


lemma ToA_mapper_MOne_tgt
  [no_atp, \<phi>reason_template default %\<phi>mapToA_derived_module_wrapper+1 name F.mapper_wrap_module_tgt]:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps a one
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps b one'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (F one) False
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (G one') False
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' F
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' G
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' G'

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I G U\<^sub>1 one' D\<^sub>I E\<^sub>1 P\<^sub>I
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F T\<^sub>1 one D\<^sub>E I\<^sub>1 P\<^sub>E

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>E (fst (h x)) \<and> D\<^sub>I (g (I\<^sub>1 (fst (h x)))))

\<Longrightarrow> \<m>\<a>\<p> (E\<^sub>1 o g o I\<^sub>1) \<otimes>\<^sub>f r : F (introduced one) \<^emph>[C\<^sub>R] R \<mapsto> G (introduced one') \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F' a \<^emph>[C\<^sub>W] W \<mapsto> G' b \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T\<^sub>1 \<^emph>[C\<^sub>R] R \<mapsto> U\<^sub>1 \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F' a \<^emph>[C\<^sub>W] W \<mapsto> G' b \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> apfst I\<^sub>1 o h \<s>\<e>\<t>\<t>\<e>\<r> s o apfst E\<^sub>1 \<i>\<n> D \<close>
  for F :: \<open>'a::plus \<Rightarrow> 'b \<Rightarrow> 'c::sep_magma set\<close>
  and T\<^sub>1 :: \<open>'b2 \<Rightarrow> 'c set\<close>
  unfolding \<r>Guard_def
  including prevent_eliminate_IE_\<phi>Cond_Unital
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
\<medium_left_bracket> premises _ and _ and _ and _ and _ and _ and _ and S1I[] and S1E[] and _ and Tr[]
  apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>x\<close>]
  apply_rule apply_Semimodule_One\<^sub>E[OF S1E, THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans]]
\<medium_right_bracket> apply(rule conjunctionI, rule)
\<medium_left_bracket> premises _ and _ and _ and _ and _ and _ and _ and S1I[] and S1E[] and _ and Tr[]
  apply_rule apply_Semimodule_One\<^sub>I[OF S1I, THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans]]
  certified by auto_sledgehammer ;;
  apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apfst E\<^sub>1 x\<close>]
  certified by (insert ToA_Mapper_f_expn[OF Tr] useful, auto_sledgehammer) ;;
\<medium_right_bracket> by(rule conjunctionI, rule, drule ToA_Mapper_f_expn_rev, clarsimp simp: Premise_def prod.map_beta)


(*
lemma ToA_mapper_MOne_tgt
  [no_atp, \<phi>reason_template default %derived_SE_inj_to_module+1 name F.mapper_wrap_module_tgt]:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps a one
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (F one) False
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' F

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F U\<^sub>1 one D\<^sub>1 I\<^sub>1 P\<^sub>E

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>(f \<otimes>\<^sub>f w) ` D. D\<^sub>1 (fst x))

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R] R \<mapsto> F' a \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T' \<^emph>[C\<^sub>W] W \<mapsto> F (introduced one) \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R] R \<mapsto> F' a \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> (I\<^sub>1 o f) \<otimes>\<^sub>f w : T' \<^emph>[C\<^sub>W] W \<mapsto> U\<^sub>1 \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> apfst I\<^sub>1 o s \<i>\<n> D \<close>
  unfolding \<r>Guard_def
  including prevent_eliminate_IE_\<phi>Cond_Unital
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
\<medium_left_bracket> premises _ and _ and _ and  S1E[] and _ and Tr[]
  apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>x\<close>]
\<medium_right_bracket> apply(rule conjunctionI, rule)
\<medium_left_bracket> premises _ and _ and _ and S1E[] and _ and Tr[]
  apply_rule ToA_Mapper_backward[OF Tr]

  apply_rule apply_Semimodule_One\<^sub>E[OF S1E, THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans]]
  certified by (insert ToA_Mapper_f_expn[OF Tr] useful, auto_sledgehammer) ;;

\<medium_right_bracket> by(rule conjunctionI, rule, drule ToA_Mapper_f_expn_rev, clarsimp)


lemma ToA_mapper_MOne_tgt'
  [no_atp, \<phi>reason_template default %derived_SE_inj_to_module name F.mapper_wrap_module_tgt']:
  \<open> \<g>\<u>\<a>\<r>\<d> partial_add_overlaps a one
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Not_Require_SA_Norm (F one) True
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F' F

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F U\<^sub>1 one D\<^sub>1 I\<^sub>1 P\<^sub>E

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in> g ` fst ` h ` D. D\<^sub>1 x)

\<Longrightarrow> \<m>\<a>\<p> (I\<^sub>1 o g) \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R] R \<mapsto> F (introduced one) \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T' \<^emph>[C\<^sub>W] W \<mapsto> F' a \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R] R \<mapsto> U\<^sub>1 \<^emph>[C\<^sub>R] R
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T' \<^emph>[C\<^sub>W] W \<mapsto> F' a \<^emph>[C\<^sub>W] W
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s o apfst I\<^sub>1 \<i>\<n> D \<close>
  for F :: \<open>'a::plus \<Rightarrow> 'b \<Rightarrow> 'c::sep_magma set\<close>
  and U\<^sub>1 :: \<open>'b2 \<Rightarrow> 'c set\<close>
  unfolding \<r>Guard_def
  including prevent_eliminate_IE_\<phi>Cond_Unital
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)
\<medium_left_bracket> premises _ and _ and _ and S1I[] and _ and Tr[]
  apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>x\<close>]
\<medium_right_bracket> apply(rule conjunctionI, rule)
\<medium_left_bracket> premises _ and _ and _ and S1I[] and _ and Tr[]

  apply_rule apply_Semimodule_One\<^sub>I[OF S1I, THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans]]
  certified by auto_sledgehammer ;;
  apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apfst I\<^sub>1 x\<close>]
  certified by auto_sledgehammer

\<medium_right_bracket> by(rule conjunctionI, rule, drule ToA_Mapper_f_expn_rev, clarsimp simp: apfst_def prod.map_comp)
*)





subsubsection \<open>Associativity\<close>

lemma scalar_assoc_template[\<phi>reason_template name Fc.scalar_assoc [assertion_simps]]:
  \<open> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt (\<lambda>_ _ _. True) smul (\<lambda>_ _ x. x)
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt (\<lambda>_ _ _. True) smul (\<lambda>_ _ x. x)
\<Longrightarrow> Ds s \<and> Dt t
\<Longrightarrow> Fs s (Ft t T) = Fc (smul s t) T \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Semimodule_Scalar_Assoc\<^sub>I_def
  by (rule \<phi>Type_eqI_Tr; simp)


lemma [\<phi>reason_template name Fc.scalar_functor [no_atp]]:
  \<open> Semimodule_Scalar_Assoc\<^sub>I Fs' Ft' Fc' U Ds' Dt' Dx' smul' f'
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> Functional_Transformation_Functor (Fs s) (Fs' s') (Ft t T) (Ft' t' U) D R pm fm
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Dt t \<and> Ds' s' \<and> Dt' t' \<and> Dx s t x \<and>
           Dx' s' t' (fm g P (f s t x)) \<and> (\<forall> a \<in> D (f s t x). g a \<in> R (f s t x))
\<Longrightarrow> (\<And>a \<in> D (f s t x). a \<Ztypecolon> Ft t T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> g a \<Ztypecolon> Ft' t' U \<w>\<i>\<t>\<h> P a )
\<Longrightarrow> x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f' s' t' (fm g P (f s t x)) \<Ztypecolon> Fc' (smul' s' t') U \<w>\<i>\<t>\<h> pm g P (f s t x) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Semimodule_Scalar_Assoc\<^sub>E_def
            Transformation_def Premise_def Functional_Transformation_Functor_def
            meta_Ball_def Action_Tag_def
  by clarsimp metis

lemma template_scalar_partial_functor[\<phi>reason_template name Fc.scalar_partial_functor [no_atp]]:
  \<open> Semimodule_Scalar_Assoc\<^sub>I Fs' Ft' Fc' U Ds' Dt' Dx' smul' f'
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> Separation_Homo\<^sub>I_Cond (Fs s) F\<^sub>W F\<^sub>s\<^sub>W C\<^sub>W (Ft t T) W Dz z
\<Longrightarrow> Separation_Homo\<^sub>E_Cond (Fs' s') F\<^sub>R F\<^sub>s\<^sub>R C\<^sub>R (Ft' t' U) R Du uz
\<Longrightarrow> Functional_Transformation_Functor F\<^sub>s\<^sub>W F\<^sub>s\<^sub>R (Ft t T \<^emph>[C\<^sub>W] W) (Ft' t' U \<^emph>[C\<^sub>R] R) D Rng pm fm
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Dt t \<and> Ds' s' \<and> Dt' t' \<and> Dx s t (fst x) \<and>
           Dx' s' t' (fst (uz (fm g P (z (apfst (f s t) x))))) \<and> apfst (f s t) x \<in> Dz \<and>
           (\<forall> a \<in> D (z (apfst (f s t) x)). g a \<in> Rng (z (apfst (f s t) x))) \<and>
           (fm g P (z (apfst (f s t) x))) \<in> Du
\<Longrightarrow> (\<And>a \<in> D (z (apfst (f s t) x)).
           a \<Ztypecolon> Ft t T \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> g a \<Ztypecolon> Ft' t' U \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P a )
\<Longrightarrow> x \<Ztypecolon> Fc (smul s t) T \<^emph>[C\<^sub>W] F\<^sub>W W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst (f' s' t') (uz (fm g P (z (apfst (f s t) x)))) \<Ztypecolon> Fc' (smul' s' t') U \<^emph>[C\<^sub>R] F\<^sub>R R
    \<w>\<i>\<t>\<h> pm g P (z (apfst (f s t) x)) \<close>
  unfolding Action_Tag_def
  \<medium_left_bracket> premises SA\<^sub>I[] and SA\<^sub>E[] and SH\<^sub>I[] and SH\<^sub>E[] and FTF[] and _ and Tr[]
    apply_rule transformation_right_frame_conditioned_ty[OF apply_Semimodule_SAssoc\<^sub>E[OF SA\<^sub>E]]
    apply_rule apply_Separation_Homo\<^sub>I_Cond[OF SH\<^sub>I]
    apply_rule apply_Functional_Transformation_Functor[OF FTF, where P=P]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Homo\<^sub>E_Cond[OF SH\<^sub>E]
    apply_rule transformation_right_frame_conditioned_ty[OF apply_Semimodule_SAssoc\<^sub>I[OF SA\<^sub>I]]
  \<medium_right_bracket> .


lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Require_Assoc_Norm (Fs s (Ft t T)) True
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> NO_SIMP (f s t x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (x \<Ztypecolon> Fs s (Ft t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding NO_SIMP_def Semimodule_Scalar_Assoc\<^sub>I_def \<r>Guard_def Premise_def
  using mk_elim_transformation by blast

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Require_Assoc_Norm (Fs s (Ft t T)) True
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> NO_SIMP (R * (f s t x \<Ztypecolon> Fc (smul s t) T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (R * (x \<Ztypecolon> Fs s (Ft t T)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Premise_def NO_SIMP_def \<r>Guard_def
  using transformation_left_frame mk_elim_transformation by blast

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Require_Assoc_Norm (Fs s (Ft t T)) False
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fc (smul s t) T \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fs s (Ft t T) \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Premise_def NO_SIMP_def \<r>Guard_def
  using mk_intro_transformation by blast

lemma [\<phi>reason_template default %ToA_derived_red]:
  \<open> \<g>\<u>\<a>\<r>\<d> Require_Assoc_Norm (Fs s (Ft t T)) False
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> Fc (smul s t) T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> NO_SIMP (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> Fs s (Ft t T) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Premise_def NO_SIMP_def \<r>Guard_def
  apply (cases C; simp)
  using transformation_left_frame mk_intro_transformation apply blast
  using mk_intro_transformation by blast

lemma [\<phi>reason_template %To_ToA_derived_SAssoc]:
  \<open> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fs s (Ft t T) \<s>\<u>\<b>\<j> y. y = f s t x @action to (\<s>\<p>\<l>\<i>\<t>-\<a>\<s>\<s>\<o>\<c> s t) \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Premise_def \<r>Guard_def Action_Tag_def
  by simp
  

paragraph \<open>ToA-based Simplification\<close>

lemma [\<phi>reason_template [\<phi>transformation_based_backward_simp default %To_ToA_derived_SAssoc no trigger]]:
  \<open> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> Fc (smul s t) T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fs s (Ft t T) \<s>\<u>\<b>\<j> y. y = f s t x @action \<A>backward_simp \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Premise_def \<r>Guard_def Action_Tag_def
  by simp

lemma [\<phi>reason_template [\<phi>transformation_based_simp default %To_ToA_derived_SAssoc no trigger]]:
  \<open> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x
\<Longrightarrow> x \<Ztypecolon> Fs s (Ft t T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Fc (smul s t) T \<s>\<u>\<b>\<j> y. y = f s t x @action \<A>simp \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Premise_def \<r>Guard_def Action_Tag_def
  by simp


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

subsubsection \<open>Scalar Distributivity\<close>

lemma [\<phi>reason_template name F.unfold_sdistr[]]:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Du uz
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F Ds Dz zi
\<Longrightarrow> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Du t s x \<and> Dz t s (uz t s x) \<and>
    zi t s (uz t s x) = x
\<Longrightarrow> (x \<Ztypecolon> F (s + t)) = (uz t s x \<Ztypecolon> F t \<^emph> F s) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Semimodule_SDistr_Homo\<^sub>S_def
  by (rule assertion_eq_intro; clarsimp simp del: split_paired_All; metis)

paragraph \<open>Checking of Non-SDistr\<close>

lemma [\<phi>reason_template 0]:
  \<open> Semimodule_No_SDistr F
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S F Ds Du uz
\<Longrightarrow> ERROR TEXT(F \<open>is declared as non-scalar-associative but a property is given\<close>
               (Semimodule_SDistr_Homo\<^sub>S F Ds Du uz)) @action \<A>_template_reason undefined
\<Longrightarrow> True\<close>
  ..

lemma [\<phi>reason_template 0]:
  \<open> Semimodule_No_SDistr F
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F Ds Du uz
\<Longrightarrow> ERROR TEXT(F \<open>is declared as non-scalar-associative but a property is given\<close>
               (Semimodule_SDistr_Homo\<^sub>Z F Ds Du uz)) @action \<A>_template_reason undefined
\<Longrightarrow> True\<close>
  ..


paragraph \<open>Zip\<close>

lemma SDirst_in_comm_scalar_implies_rev\<^sub>Z
      [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice,
       \<phi>adding_property = true]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F Ds Dx z Dx z\<close>
  for F :: \<open>('s::partial_ab_semigroup_add \<Rightarrow> ('c::sep_magma,'a) \<phi>)\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_rev_def Semimodule_SDistr_Homo\<^sub>Z_def
  by (simp add: dom_of_add_commute partial_add_commute)

lemma SDirst_in_comm_sep_implies_rev\<^sub>Z
      [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice-1,
       \<phi>adding_property = true]:
  \<open> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z_rev F Ds Dx z (\<lambda>s t. Dx t s o prod.swap) (\<lambda>s t. z t s o prod.swap)\<close>
  for F :: \<open>('s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup,'a) \<phi>)\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_rev_def Semimodule_SDistr_Homo\<^sub>Z_def
  by (simp add: \<phi>Prod_expn'; metis mult.commute)


paragraph \<open>Unzip\<close>

lemma SDirst_in_comm_scalar_implies_rev\<^sub>U
      [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice,
       \<phi>adding_property = true]:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S_rev F Dx uz Ds Dx uz\<close>
  for F :: \<open>('s::partial_ab_semigroup_add \<Rightarrow> ('c::sep_magma,'a) \<phi>)\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_rev_def Semimodule_SDistr_Homo\<^sub>S_def
  by (simp add: dom_of_add_commute partial_add_commute)

lemma SDirst_in_comm_sep_implies_rev\<^sub>U
      [\<phi>adding_property = false,
       \<phi>reason default %\<phi>TA_fallback_lattice-1,
       \<phi>adding_property = true]:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx z
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S_rev F Dx uz Ds (\<lambda>s t. Dx t s) (\<lambda>s t. prod.swap o z t s)\<close>
  for F :: \<open>('s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup,'a) \<phi>)\<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_rev_def Semimodule_SDistr_Homo\<^sub>S_def
  by (clarsimp simp add: \<phi>Prod_expn'' mult.commute)

lemma [\<phi>reason_template %To_ToA_derived_SDistri]:
  \<open> Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> s ##\<^sub>+ t \<and> Dx t s x
\<Longrightarrow> x \<Ztypecolon> F (s + t) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F t \<^emph> F s \<s>\<u>\<b>\<j> y. y = uz t s x @action to (\<s>\<p>\<l>\<i>\<t>-\<s>\<c>\<a>\<l>\<a>\<r> s t) \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_def Premise_def Action_Tag_def
  by simp


subsection \<open>Separation Extraction\<close>

subsubsection \<open>Transformation Functor\<close>

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

 




lemma "_Structural_Extract_general_rule_i_"[\<phi>reason_template default %derived_SE_functor name F\<^sub>1.separation_extraction]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F\<^sub>1\<^sub>4 F\<^sub>2\<^sub>3 (T \<^emph>[Cw] W) (U \<^emph>[Cr] R) Dom Rng pred_mapper func_mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>I_Cond F\<^sub>1 F\<^sub>4 F\<^sub>1\<^sub>4 Cw T W Dz z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>E_Cond F\<^sub>3 F\<^sub>2 F\<^sub>2\<^sub>3 Cr U R Du uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (y = uz (func_mapper f P (z x)) \<longrightarrow>
              x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x)) \<and> func_mapper f P (z x) \<in> Du)
\<Longrightarrow> (\<And>a \<in> Dom (z x). \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> y = uz (func_mapper f P (z x)) \<Longrightarrow> a \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f a \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P a )
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> y : uz (func_mapper f P (z x)) 
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 T \<^emph>[Cw] F\<^sub>4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 U \<^emph>[Cr] F\<^sub>2 R \<w>\<i>\<t>\<h> pred_mapper f P (z x) \<close>
  unfolding \<r>Guard_def
  \<medium_left_bracket> premises FTF[] and SH\<^sub>I[] and SH\<^sub>E[] and _ and Tr and _
    apply_rule apply_Separation_Homo\<^sub>I_Cond[where Fu=F\<^sub>4 and Ft=F\<^sub>1, OF SH\<^sub>I]
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
               else if Cr then (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> f (a, unspec) \<in> Rng'w (fst x))
                          else (\<forall>a. a \<in> Dom'w (fst x) \<longrightarrow> fst (f (a, unspec)) \<in> Rng'b (fst x)))

\<Longrightarrow> (\<And>x \<in> (if Cw then Dom (z x) else Dom'w (fst x) \<times> {unspec}).
        x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h>
            Auto_Transform_Hint (y1\<^sub>H \<Ztypecolon> U\<^sub>H \<^emph>[Cr] R\<^sub>H) (x1\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph>[Cw] W\<^sub>H) \<and> P x )

\<Longrightarrow> x \<Ztypecolon> F1 T \<^emph>[Cw] F4 W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if Cw then if Cr then uz (func_mapper f P (z x))
                                else (func_mapper'r (fst o f) P (z x), unspec)
                     else if Cr then uz (func_mapper'w (\<lambda>x. f (x, unspec)) (\<lambda>x. P (x, unspec)) (fst x))
                                else (func_mapper'b (\<lambda>x. fst (f (x, unspec))) (\<lambda>x. P (x, unspec)) (fst x), unspec))
                \<Ztypecolon> F3 U \<^emph>[Cr] F2 R

    \<w>\<i>\<t>\<h> Auto_Transform_Hint (y2\<^sub>H \<Ztypecolon> F3' U\<^sub>H \<^emph>[Cr] F2' R\<^sub>H) (x2\<^sub>H \<Ztypecolon> F1' T\<^sub>H \<^emph>[Cw] F4' W\<^sub>H)
      \<and> (if Cw then if Cr then pred_mapper f P (z x) else pred_mapper'r (fst o f) P (z x)
               else if Cr then pred_mapper'w (\<lambda>x. f (x, unspec)) (\<lambda>x. P (x, unspec)) (fst x)
                          else pred_mapper'b (\<lambda>x. fst (f (x, unspec))) (\<lambda>x. P (x, unspec)) (fst x) )
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

subparagraph \<open>With Parameterization\<close>

lemma "_Structural_Extract\<^sub>\<Lambda>_general_rule_i_"[\<phi>reason_template default %derived_SE_functor]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor\<^sub>\<Lambda> F\<^sub>1\<^sub>4 F\<^sub>2\<^sub>3 (\<lambda>p. T p \<^emph>[Cw] W p) (\<lambda>p. U p \<^emph>[Cr] R p) Dom Rng pred_mapper func_mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond F\<^sub>1 F\<^sub>4 F\<^sub>1\<^sub>4 Cw T W Dz z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond F\<^sub>3 F\<^sub>2 F\<^sub>2\<^sub>3 Cr U R Du uz
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (y = uz (func_mapper f P (z x))  \<longrightarrow>
        x \<in> Dz \<and> (\<forall>p a. a \<in> Dom p (z x) \<longrightarrow> f p a \<in> Rng p (z x)) \<and> func_mapper f P (z x) \<in> Du)
\<Longrightarrow> (\<And>p. \<And>a \<in> Dom p (z x). \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> y = uz (func_mapper f P (z x)) \<Longrightarrow>
          a \<Ztypecolon> T p \<^emph>[Cw] W p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f p a \<Ztypecolon> U p \<^emph>[Cr] R p \<w>\<i>\<t>\<h> P p a )
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> y : uz (func_mapper f P (z x)) 
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 T \<^emph>[Cw] F\<^sub>4 W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 U \<^emph>[Cr] F\<^sub>2 R \<w>\<i>\<t>\<h> pred_mapper f P (z x) \<close>
  unfolding \<r>Guard_def
  \<medium_left_bracket> premises FTF[] and SH\<^sub>I[] and SH\<^sub>E[] and _ and Tr and _
    apply_rule apply_Separation_Homo\<^sub>\<Lambda>\<^sub>I_Cond[where Fu=F\<^sub>4 and Ft=F\<^sub>1, OF SH\<^sub>I]
    apply_rule apply_Functional_Transformation_Functor\<^sub>\<Lambda>[where U=\<open>\<lambda>p. U p \<^emph>[Cr] R p\<close> and f=\<open>f\<close> and P=\<open>P\<close>, OF FTF]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Homo\<^sub>\<Lambda>\<^sub>E_Cond[OF SH\<^sub>E]
  \<medium_right_bracket> .


subsubsection \<open>Transformation Mapper\<close>


declare [[\<phi>trace_reasoning = 1]]

context 
  notes BiCond_assoc[simp] BiCond_assoc'[simp] \<phi>Prod_expn''[simp, \<phi>programming_simps]
        prod_opr_norm[simp] boolean_conversions[simp]
begin

lemma ToA_mapper_template[\<phi>reason_template default %\<phi>mapToA_derived_TF name F\<^sub>1.ToA_mapper]:
  \<open> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F\<^sub>1\<^sub>4 F\<^sub>2\<^sub>3 (T \<^emph>[C\<^sub>W] W) (U \<^emph>[C\<^sub>R] R) Dom Rng pred_mapper func_mapper
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Parameter_Variant_of_the_Same_Type (F\<^sub>1\<^sub>4 (T \<^emph>[C\<^sub>W] W)) (F\<^sub>1\<^sub>4' (T' \<^emph>[C\<^sub>W] W'))
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Functional_Transformation_Functor F\<^sub>2\<^sub>3' F\<^sub>1\<^sub>4' (U' \<^emph>[C\<^sub>R] R') (T' \<^emph>[C\<^sub>W] W') Dom' Rng' pred_mapper' func_mapper'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>I_Cond F\<^sub>1 F\<^sub>4 F\<^sub>1\<^sub>4 C\<^sub>W T W Dz z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>I_Cond F\<^sub>3' F\<^sub>2' F\<^sub>2\<^sub>3' C\<^sub>R U' R' Dz' z'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>E_Cond F\<^sub>3 F\<^sub>2 F\<^sub>2\<^sub>3 C\<^sub>R U R Du uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Separation_Homo\<^sub>E_Cond F\<^sub>1' F\<^sub>4' F\<^sub>1\<^sub>4' C\<^sub>W T' W' Du' uz'
\<Longrightarrow> compositional_mapper m\<^sub>1 (\<lambda>h. func_mapper h (\<lambda>_. True)) m\<^sub>2 Dm\<^sub>1 (g \<otimes>\<^sub>f r) h @action \<A>_template_reason undefined
\<Longrightarrow> separatable_cond_unzip C\<^sub>R z' uz Du\<^sub>s m\<^sub>1 m\<^sub>g m\<^sub>r g r @action \<A>_template_reason undefined
\<Longrightarrow> compositional_mapper (\<lambda>s. func_mapper' s (\<lambda>_. True)) m\<^sub>2 m\<^sub>3 Dm\<^sub>2 s (g \<otimes>\<^sub>f r o h) @action \<A>_template_reason undefined
\<Longrightarrow> separatable_cond_zip C\<^sub>W uz' z Dz\<^sub>s m\<^sub>3 m\<^sub>f m\<^sub>w f w @action \<A>_template_reason undefined
\<Longrightarrow> domain_by_mapper Dom' m\<^sub>2 Dom (g \<otimes>\<^sub>f r o h) D\<^sub>d\<^sub>m @action \<A>_template_reason undefined
\<Longrightarrow> domain_of_inner_map m\<^sub>3 Dm\<^sub>3 @action \<A>_template_reason undefined
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : U \<^emph>[C\<^sub>R] R \<mapsto> U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> \<Union> (Dom ` z ` D)

\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>[\<s>\<a>\<f>\<e>] (C\<^sub>R \<or> r = (\<lambda>_. unspec)) \<and> (C\<^sub>W \<or> w = (\<lambda>_. unspec))

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D.
      x \<in> Dz \<and> x \<in> Dz\<^sub>s \<and> z x \<in> Dm\<^sub>1 \<and> z x \<in> Dm\<^sub>2 \<and> z x \<in> D\<^sub>d\<^sub>m \<and>
      (\<forall>a \<in> Dm\<^sub>3 (z x). a \<in> Dom (z x)) \<and>
      (\<forall>a \<in> Dom (z x). h a \<in> Rng (z x)) \<and>
      (let x\<^sub>1 = func_mapper h  (\<lambda>_. True) (z x) in
            x\<^sub>1 \<in> Du \<and> x\<^sub>1 \<in> Du\<^sub>s \<and>
            (m\<^sub>g g \<otimes>\<^sub>f m\<^sub>r r) (uz x\<^sub>1) \<in> Dz' \<and>
            (\<forall>a \<in> Dom' (m\<^sub>2 (g \<otimes>\<^sub>f r o h) (z x)). s a \<in> Rng' (m\<^sub>2 (g \<otimes>\<^sub>f r o h) (z x))) \<and>
            m\<^sub>3 (f \<otimes>\<^sub>f w) (z x) \<in> Du') )

\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> h' : uz o func_mapper h (\<lambda>_. True) o z @action \<A>_template_reason undefined
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> s' : uz' o func_mapper' s (\<lambda>_. True) o z' @action \<A>_template_reason undefined
\<Longrightarrow> \<m>\<a>\<p> m\<^sub>g g \<otimes>\<^sub>f m\<^sub>r r : F\<^sub>3 U \<^emph>[C\<^sub>R] F\<^sub>2 R \<mapsto> F\<^sub>3' U' \<^emph>[C\<^sub>R] F\<^sub>2' R'
    \<o>\<v>\<e>\<r> m\<^sub>f f \<otimes>\<^sub>f m\<^sub>w w : F\<^sub>1 T \<^emph>[C\<^sub>W] F\<^sub>4 W \<mapsto> F\<^sub>1' T' \<^emph>[C\<^sub>W] F\<^sub>4' W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h' \<s>\<e>\<t>\<t>\<e>\<r> s' \<i>\<n> D\<close>

  unfolding \<r>Guard_def Action_Tag_def separatable_unzip_def compositional_mapper_def
            separatable_zip_def domain_of_inner_map_def NO_SIMP_def domain_by_mapper_def
            separatable_cond_unzip_def separatable_cond_zip_def
  \<medium_left_bracket> premises FTF[] and [] and FTF'[] and SH\<^sub>I[] and SH\<^sub>I'[] and SH\<^sub>E[] and SH\<^sub>E'[]
         and [useful] and [useful] and [useful] and [useful] and [useful] and [] and Tr
         and [] and _ and [simp] and [simp]
    apply_rule apply_Separation_Homo\<^sub>I_Cond[where Fu=F\<^sub>4 and Ft=F\<^sub>1, OF SH\<^sub>I]
    apply_rule apply_Functional_Transformation_Functor[where U=\<open>U \<^emph>[C\<^sub>R] R\<close> and f=\<open>h\<close> and P=\<open>\<lambda>_. True\<close>, OF FTF]
    \<medium_left_bracket> apply_rule ToA_Mapper_onward[OF Tr] \<medium_right_bracket>
    apply_rule apply_Separation_Homo\<^sub>E_Cond[OF SH\<^sub>E] certified by (metis the_\<phi>(3) the_\<phi>(4))
  \<medium_right_bracket> apply (rule conjunctionI, rule, simp add: image_image del: split_paired_All)
  \<medium_left_bracket> premises FTF[] and [] and FTF'[] and SH\<^sub>I[] and SH\<^sub>I'[] and SH\<^sub>E[] and SH\<^sub>E'[]
         and [useful] and [useful] and [useful] and [useful] and DM and DiM and Tr
         and t3 and _ and [simp] and [simp]
    ;; apply_rule apply_Separation_Homo\<^sub>I_Cond[OF SH\<^sub>I']
    certified by (insert useful(1), simp add: image_iff, elim bexE, metis the_\<phi>(4)) ;;
  
    apply_rule apply_Functional_Transformation_Functor[where f=s and P=\<open>\<lambda>_. True\<close>, OF FTF']
    \<medium_left_bracket> for a
      apply_rule ToA_Mapper_backward[OF Tr]
      certified proof (insert \<open>a \<in> Dom' (z' x)\<close> \<open>x \<in> (\<lambda>x. (m\<^sub>g g \<otimes>\<^sub>f m\<^sub>r r) (uz (func_mapper h (\<lambda>_. True) (z x)))) ` D\<close>,
                      simp add: image_iff, elim bexE)
                  fix xa :: "'o \<times> 'p"
                  assume a1: "xa \<in> D"
                  assume a2: "a \<in> Dom' (z' x)"
                  assume a3: "x = (m\<^sub>g g \<otimes>\<^sub>f m\<^sub>r r) (uz (func_mapper h (\<lambda>_. True) (z xa)))"
                  have t1: "func_mapper h (\<lambda>p. True) (z xa) \<in> Du\<^sub>s"
                    using a1 by (metis (no_types) the_\<phi>(5))
                  show "\<exists>p\<in>D. \<exists>p\<in>Dom (z p). a = (g \<otimes>\<^sub>f r) (h p)"
                  proof (rule bexI[OF _ a1])
                    have "\<forall>P p f. \<exists>pa. ((p::'l \<times> 'm) \<notin> f ` P \<or> (pa::'a \<times> 'b) \<in> P) \<and> (p \<notin> f ` P \<or> f pa = p)"
                      by blast
                    then show "\<exists>p\<in>Dom (z xa). a = (g \<otimes>\<^sub>f r) (h p)"
                      by (smt (z3) DM a1 a2 a3 subset_iff the_\<phi>(11) the_\<phi>(12) the_\<phi>(5) the_\<phi>(7))
                  qed
                qed 
    \<medium_right_bracket> ;; certified by (insert useful(1), simp add: image_iff, elim bexE,
                       metis the_\<phi>(10) the_\<phi>(3) the_\<phi>(5) the_\<phi>(9)) ;;
    apply_rule apply_Separation_Homo\<^sub>E_Cond[OF SH\<^sub>E']
    certified proof -
        obtain y where t1: \<open>y \<in> D\<close> and t2: \<open>x = (m\<^sub>g g \<otimes>\<^sub>f m\<^sub>r r) (uz (func_mapper h (\<lambda>_. True) (z y)))\<close>
          by (insert useful(2), blast)
        have t3: \<open>Dm\<^sub>3 (z y) \<subseteq> Dom (z y)\<close>
          using t1 the_\<phi>(4) by fastforce
        have t4: \<open>m\<^sub>3 (s \<circ> (g \<otimes>\<^sub>f r \<circ> h)) (z y) = m\<^sub>3 (f \<otimes>\<^sub>f w) (z y)\<close>
          by (insert ToA_Mapper_f_expn[OF Tr], clarsimp,
              metis (mono_tags, opaque_lifting) DiM comp_apply t1 the_\<phi>(4))
        show ?thesis
          by (insert \<open>\<forall>x\<in>D. _\<close>[THEN bspec[OF _ t1]], simp add: t2 t4[symmetric],
              metis the_\<phi>(10) the_\<phi>(11) the_\<phi>(6) the_\<phi>(9))
      qed
  \<medium_right_bracket> apply (rule conjunctionI, simp, drule ToA_Mapper_f_expn,
        simp add: Premise_def Simplify_def subset_iff del: split_paired_All,
        rule)
    subgoal premises prems for x
    proof -
      have t1: \<open>Dm\<^sub>3 (z x) \<subseteq> Dom (z x)\<close>
        using prems(15) prems(19) by blast
      have t2: \<open>m\<^sub>3 (s \<circ> (g \<otimes>\<^sub>f r \<circ> h)) (z x) = m\<^sub>3 (f \<otimes>\<^sub>f w) (z x)\<close>
        by (rule \<open>\<forall>f g x. (\<forall>a\<in>Dm\<^sub>3 x. f a = g a) \<longrightarrow> m\<^sub>3 f x = m\<^sub>3 g x\<close>[THEN spec, THEN spec, THEN spec, THEN mp],
            metis comp_def prems(18) prems(19) subset_iff t1)
      show ?thesis
        by (metis prems(10) prems(11) prems(14) prems(15) prems(19) prems(8) prems(9) t2)
    qed .


end


subsubsection \<open>Semimodule Scalar Associative \label{Semimodule-Scalar-Associative}\<close>

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

lemma SE_Semimodule_Scalar_right
      [\<phi>reason_template default %derived_SE_scalar_assoc name: F3\<^sub>b.ToR_scala_assoc_right]:
  \<open> \<g>\<u>\<a>\<r>\<d> common_multiplicator_2 smul a c b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D\<^sub>a a \<and> D\<^sub>c c
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I F3\<^sub>a F3\<^sub>c F3\<^sub>b U D\<^sub>a D\<^sub>c D\<^sub>x smul g\<^sub>s
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F3\<^sub>a F1
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F3\<^sub>a F4
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F3\<^sub>a F2
\<Longrightarrow> Functional_Transformation_Functor (F1 a) (F3\<^sub>a a) T (F3\<^sub>c c U) Dom Rng pred_mapper func_mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>a. a \<in> Dom x \<longrightarrow> f a \<in> Rng x) \<and> D\<^sub>x a c (func_mapper f P x)
\<Longrightarrow> (\<And>x \<in> Dom x. x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F3\<^sub>c c U \<w>\<i>\<t>\<h> P x)
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> g\<^sub>s a c (func_mapper f P x) \<Ztypecolon> F3\<^sub>b b U
    \<w>\<i>\<t>\<h> pred_mapper f P x \<close>
  unfolding \<r>Guard_def common_multiplicator_2_def
  \<medium_left_bracket> premises [simp] and _ and SA[] and _ and _ and _ and FTF[] and _ and Tr[]
    apply_rule apply_Functional_Transformation_Functor[where f=f and P=P, OF FTF]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Semimodule_SAssoc\<^sub>I[OF SA]
  \<medium_right_bracket> .

lemma SE_Semimodule_Scalar_left
      [\<phi>reason_template default %derived_SE_scalar_assoc name: F1\<^sub>b.ToR_scala_assoc_left]:
  \<open> \<g>\<u>\<a>\<r>\<d> common_multiplicator_2 smul a c b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D\<^sub>a a \<and> D\<^sub>c c
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E F1\<^sub>a F1\<^sub>c F1\<^sub>b T D\<^sub>a D\<^sub>c D\<^sub>x smul g\<^sub>s
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1\<^sub>a F3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1\<^sub>a F4
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1\<^sub>a F2
\<Longrightarrow> Functional_Transformation_Functor (F1\<^sub>a a) (F3 a) (F1\<^sub>c c T) U Dom Rng pred_mapper func_mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D\<^sub>x a c x \<and> (\<forall>e \<in> Dom (g\<^sub>s a c x). f e \<in> Rng (g\<^sub>s a c x)) \<and>
           func_mapper f P (g\<^sub>s a c x) \<in> Du
\<Longrightarrow> (\<And>x \<in> Dom (g\<^sub>s a c x). x \<Ztypecolon> F1\<^sub>c c T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<w>\<i>\<t>\<h> P x )
\<Longrightarrow> x \<Ztypecolon> F1\<^sub>b b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> func_mapper f P (g\<^sub>s a c x) \<Ztypecolon> F3 a U
    \<w>\<i>\<t>\<h> pred_mapper f P (g\<^sub>s a c x) \<close>
  unfolding \<r>Guard_def common_multiplicator_2_def
  \<medium_left_bracket> premises A and _ and SA[] and _ and _ and _ and FTF[] and _ and Tr[]
    apply_rule apply_Semimodule_SAssoc\<^sub>E[where s=a and t=c and smul=smul, OF SA, unfolded A]
    apply_rule apply_Functional_Transformation_Functor[where f=f and P=P, OF FTF]
    \<medium_left_bracket> Tr \<medium_right_bracket>
  \<medium_right_bracket> .


 
lemma SE_Semimodule_Scalar_partial_right:
  \<open> \<g>\<u>\<a>\<r>\<d> common_multiplicator_2 smul a c b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D\<^sub>a a \<and> D\<^sub>c c
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I F3\<^sub>a F3\<^sub>c F3\<^sub>b U D\<^sub>a D\<^sub>c D\<^sub>x smul g\<^sub>s
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F3\<^sub>a F1
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F3\<^sub>a F4
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F3\<^sub>a F2
\<Longrightarrow> Separation_Homo\<^sub>I_Cond (F1 a) (F4 a) F14 Cw T W Dz z
\<Longrightarrow> Separation_Homo\<^sub>E_Cond (F3\<^sub>a a) (F2 a) F23 Cr (F3\<^sub>c c U) R Du uz
\<Longrightarrow> Functional_Transformation_Functor F14 F23 (T \<^emph>[Cw] W) (F3\<^sub>c c U \<^emph>[Cr] R) Dom Rng pred_mapper func_mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> x \<in> Dz \<and> (\<forall>a. a \<in> Dom (z x) \<longrightarrow> f a \<in> Rng (z x)) \<and>
           func_mapper f P (z x) \<in> Du \<and>
           D\<^sub>x a c (fst (uz (func_mapper f P (z x))))
\<Longrightarrow> (\<And>x \<in> Dom (z x). x \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F3\<^sub>c c U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P x )
\<Longrightarrow> x \<Ztypecolon> F1 a T \<^emph>[Cw] F4 a W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> apfst (g\<^sub>s a c) (uz (func_mapper f P (z x))) \<Ztypecolon> F3\<^sub>b b U \<^emph>[Cr] F2 a R
    \<w>\<i>\<t>\<h> pred_mapper f P (z x) \<close>
  unfolding \<r>Guard_def common_multiplicator_2_def
  \<medium_left_bracket> premises [simp] and _ and SA and _ and _ and _ and SH\<^sub>I and SH\<^sub>E and FTF and _ and Tr
    apply_rule apply_Separation_Homo\<^sub>I_Cond[OF SH\<^sub>I]
    apply_rule apply_Functional_Transformation_Functor[where f=f and P=P, OF FTF]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Homo\<^sub>E_Cond[OF SH\<^sub>E]
    apply_rule apply_Semimodule_SAssoc\<^sub>I[OF SA, THEN transformation_right_frame_conditioned_ty]
  \<medium_right_bracket> .

declare SE_Semimodule_Scalar_partial_right[(*THEN SE_clean_waste,*)
    \<phi>reason_template default %derived_SE_scalar_assoc name: F3\<^sub>b.ToR_scala_assoc_partial_right]


lemma SE_Semimodule_Scalar_partial_left
      [\<phi>reason_template default %derived_SE_scalar_assoc name: F1\<^sub>b.ToR_scala_assoc_partial_left]:
  \<open> \<g>\<u>\<a>\<r>\<d> common_multiplicator_2 smul a c b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D\<^sub>a a \<and> D\<^sub>c c
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E F1\<^sub>a F1\<^sub>c F1\<^sub>b T D\<^sub>a D\<^sub>c D\<^sub>x smul g\<^sub>s
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1\<^sub>a F3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1\<^sub>a F4
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1\<^sub>a F2
\<Longrightarrow> Separation_Homo\<^sub>I_Cond (F1\<^sub>a a) (F4 a) F14 Cw (F1\<^sub>c c T) W Dz z
\<Longrightarrow> Separation_Homo\<^sub>E_Cond (F3 a) (F2 a) F23 Cr U R Du uz
\<Longrightarrow> Functional_Transformation_Functor F14 F23 (F1\<^sub>c c T \<^emph>[Cw] W) (U \<^emph>[Cr] R) Dom Rng pred_mapper func_mapper
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> apfst (g\<^sub>s a c) x \<in> Dz \<and> D\<^sub>x a c (fst x) \<and>
           (\<forall>e \<in> Dom (z (apfst (g\<^sub>s a c) x)). f e \<in> Rng (z (apfst (g\<^sub>s a c) x))) \<and>
           func_mapper f P (z (apfst (g\<^sub>s a c) x)) \<in> Du
\<Longrightarrow> (\<And>x \<in> Dom (z (apfst (g\<^sub>s a c) x)). x \<Ztypecolon> F1\<^sub>c c T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P x )
\<Longrightarrow> x \<Ztypecolon> F1\<^sub>b b T \<^emph>[Cw] F4 a W
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz (func_mapper f P (z (apfst (g\<^sub>s a c) x))) \<Ztypecolon> F3 a U \<^emph>[Cr] F2 a R
    \<w>\<i>\<t>\<h> pred_mapper f P (z (apfst (g\<^sub>s a c) x)) \<close>
  unfolding \<r>Guard_def common_multiplicator_2_def
  \<medium_left_bracket> premises A and _ and SA[] and _ and _ and _ and SH\<^sub>I[] and SH\<^sub>E[] and FTF[] and _ and Tr[]
    apply_rule apply_Semimodule_SAssoc\<^sub>E[where s=a and t=c and smul=smul, OF SA, THEN transformation_right_frame_conditioned_ty, unfolded A]
    apply_rule apply_Separation_Homo\<^sub>I_Cond[OF SH\<^sub>I]
    apply_rule apply_Functional_Transformation_Functor[where f=f and P=P, OF FTF]
    \<medium_left_bracket> Tr \<medium_right_bracket>
    apply_rule apply_Separation_Homo\<^sub>E_Cond[OF SH\<^sub>E]
  \<medium_right_bracket> .

paragraph \<open>Transformation Mapper\<close>


lemma SE_Module_scalar_assoc_mapper_tgt_template
      [no_atp, \<phi>reason_template default %\<phi>mapToA_derived_module_assoc name F\<^sub>3\<^sub>b.assoc_mapper_tgt]:
  \<open> \<g>\<u>\<a>\<r>\<d> common_multiplicator_2 smul a c b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D\<^sub>a a \<and> D\<^sub>c c
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I F\<^sub>3\<^sub>a F\<^sub>3\<^sub>c F\<^sub>3\<^sub>b U D\<^sub>a D\<^sub>c D\<^sub>x smul g\<^sub>I
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F\<^sub>3\<^sub>a F\<^sub>3\<^sub>a'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F\<^sub>3\<^sub>a F\<^sub>1
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F\<^sub>3\<^sub>a F\<^sub>1'
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E F\<^sub>3\<^sub>a' F\<^sub>3\<^sub>c' F\<^sub>3\<^sub>b' U' D\<^sub>a D\<^sub>c D\<^sub>x' smul g\<^sub>E

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>x a c (fst (h x)) \<and> D\<^sub>x' a c (g (g\<^sub>I a c (fst (h x)))))

\<Longrightarrow> \<m>\<a>\<p> (g\<^sub>E a c o g o g\<^sub>I a c) \<otimes>\<^sub>f r : F\<^sub>3\<^sub>a a (F\<^sub>3\<^sub>c c U) \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3\<^sub>a' a (F\<^sub>3\<^sub>c' c U') \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 a T \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1' a T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3\<^sub>b b U \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3\<^sub>b' b U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 a T \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1' a T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> apfst (g\<^sub>I a c) o h \<s>\<e>\<t>\<t>\<e>\<r> s o apfst (g\<^sub>E a c)
      \<i>\<n> D \<close>
  unfolding \<r>Guard_def common_multiplicator_2_def
  including prevent_eliminate_IE_\<phi>Cond_Unital
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)

\<medium_left_bracket> premises A and _ and SA\<^sub>I[] and [] and [] and [] and SA\<^sub>E[] and _ and Tr[]
  apply_rule ToA_Mapper_onward[OF Tr, where x=x]
  apply_rule apply_Semimodule_SAssoc\<^sub>I[where s=a and t=c, OF SA\<^sub>I,
                THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans], unfolded A]
\<medium_right_bracket> apply (rule conjunctionI, rule)
\<medium_left_bracket> premises A and _ and SA\<^sub>I[] and [] and [] and [] and SA\<^sub>E[] and _ and Tr[] 
  apply_rule apply_Semimodule_SAssoc\<^sub>E[where s=a and t=c, OF SA\<^sub>E,
                THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans], unfolded A]
    certified by auto_sledgehammer ;;
  apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apfst (g\<^sub>E a c) x\<close>]
    certified by (insert ToA_Mapper_f_expn[OF Tr], auto_sledgehammer)
\<medium_right_bracket> by (rule conjunctionI, rule, drule ToA_Mapper_f_expn, clarsimp simp: prod.map_beta)


lemma SE_Module_scalar_assoc_mapper_src_template
      [no_atp, \<phi>reason_template default %\<phi>mapToA_derived_module_assoc name F\<^sub>3\<^sub>b.assoc_mapper_src]:
  \<open> \<g>\<u>\<a>\<r>\<d> common_multiplicator_2 smul a c b
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D\<^sub>a a \<and> D\<^sub>c c
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E F\<^sub>3\<^sub>a F\<^sub>3\<^sub>c F\<^sub>3\<^sub>b U D\<^sub>a D\<^sub>c D\<^sub>x smul g\<^sub>E
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F\<^sub>3\<^sub>a F\<^sub>3\<^sub>a'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F\<^sub>3\<^sub>a F\<^sub>1
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F\<^sub>3\<^sub>a F\<^sub>1'
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I F\<^sub>3\<^sub>a' F\<^sub>3\<^sub>c' F\<^sub>3\<^sub>b' U' D\<^sub>a D\<^sub>c D\<^sub>x' smul g\<^sub>I

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>x a c (fst x) \<and> D\<^sub>x' a c (f (g\<^sub>E a c (fst x))))

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>1 a T \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>1' a T' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>3\<^sub>a a (F\<^sub>3\<^sub>c c U) \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>3\<^sub>a' a (F\<^sub>3\<^sub>c' c U') \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> apfst (g\<^sub>E a c) ` D

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>1 a T \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>1' a T' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> (g\<^sub>I a c o f o g\<^sub>E a c) \<otimes>\<^sub>f w : F\<^sub>3\<^sub>b b U \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>3\<^sub>b' b U' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h o apfst (g\<^sub>E a c) \<s>\<e>\<t>\<t>\<e>\<r> apfst (g\<^sub>I a c) o s
      \<i>\<n> D \<close>
  unfolding \<r>Guard_def common_multiplicator_2_def
  including prevent_eliminate_IE_\<phi>Cond_Unital
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)

\<medium_left_bracket> premises A and _ and SA\<^sub>E[] and [] and [] and [] and SA\<^sub>I[] and _ and Tr[]
  apply_rule apply_Semimodule_SAssoc\<^sub>E[where s=a and t=c, OF SA\<^sub>E,
                THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans], unfolded A]
  apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>apfst (g\<^sub>E a c) x\<close>]
\<medium_right_bracket> apply (rule conjunctionI, rule)
\<medium_left_bracket> premises A and _ and SA\<^sub>E[] and [] and [] and [] and SA\<^sub>I[] and _ and Tr[] 
  apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>x\<close>]
  apply_rule apply_Semimodule_SAssoc\<^sub>I[where s=a and t=c, OF SA\<^sub>I,
                THEN \<phi>Some_transformation_strip[THEN verit_Pure_trans], unfolded A]
  certified by (insert ToA_Mapper_f_expn[OF Tr], auto_sledgehammer)
\<medium_right_bracket> by (rule conjunctionI, rule, drule ToA_Mapper_f_expn, clarsimp, auto_sledgehammer)




subparagraph \<open>With Parameterization\<close>

(* TODO!
lemma SE_general_Semimodule_Scalar_left_b: (*need test, to be tested once we have usable test case*)
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> smul a c = b)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D\<^sub>a a \<and> D\<^sub>c c
\<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> F14 F23 (T \<^emph>[Cw] W) (F3\<^sub>c c U \<^emph>[Cr] R) Dom Rng pred_mapper func_mapper
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
*)


subsection \<open>Separation Extraction of Semimodule Left Distributivity\<close>

paragraph \<open>Commutative, Non-Unital Associative, No Additive Zero\<close>

text \<open>Non-unital algebra implies no additive zero.\<close>

ML_file \<open>library/phi_type_algebra/semimodule_rule_pass.ML\<close>

(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; the scalar has to be non-commutative, otherwise reduces to either \<open>SE_Module_SDistr_da_b_i\<close> or \<open>SE_Module_SDistr_a_cb_i\<close>
   as we assume non-commutative scalar, the concrete algebra must be commutative*)
lemma SE_Module_SDistr_da_bc
      [where Cr'=True, \<phi>reason_template default %derived_SE_sdistr pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> dabc_equation d a b c)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d (fst x, x\<^sub>d) \<and> Dx c b (z a d (fst x,x\<^sub>d))
\<Longrightarrow> (snd (uz c b (z a d (fst x, x\<^sub>d))), w) \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> ((snd y, fst (uz c b (z a d (fst x, x\<^sub>d)))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[True] F\<^sub>1 c) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close> 
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (drule dabc_equation_D_main,
         simp add: cond_prod_transformation_rewr;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises SD\<^sub>U[] and SD\<^sub>Z[] and _ and _ and _ and Tr and _ and b and [simp]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F\<^sub>1 and x=\<open>(fst x,x\<^sub>d)\<close>, OF SD\<^sub>Z]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[where t=c and s=b and F=F\<^sub>1, OF SD\<^sub>U]
    Tr
    apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F\<^sub>3 b\<close>]]
  \<medium_right_bracket> .


(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; the scalar has to be non-commutative, otherwise reduces to either \<open>SE_Module_SDistr_da_b_i\<close> or \<open>SE_Module_SDistr_a_cb_i\<close>
   as we assume non-commutative scalar, the concrete algebra must be commutative*)
lemma SE_Module_SDistr_ad_cb
      [where Cw' = True, \<phi>reason_template default %derived_SE_sdistr pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> dabc_equation c b a d)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' d a (x\<^sub>d, fst x) \<and> Dx b c (z d a (x\<^sub>d, fst x))
\<Longrightarrow> (fst (uz b c (z d a (x\<^sub>d, fst x))), w) \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> ((snd (uz b c (z d a (x\<^sub>d, fst x))), snd y) \<Ztypecolon> \<half_blkcirc>[True] F\<^sub>1 c \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (drule dabc_equation_D_main;
         simp add: cond_prod_transformation_rewr conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises _ and _ and _ and _ and _ and Tr and [simp] and b and [symmetric, simp] and [simp] and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=d and s=a and F=F\<^sub>1 and x=\<open>(x\<^sub>d, fst x)\<close>]
       apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[where t=b and s=c and F=F\<^sub>1]
       Tr
       b
  \<medium_right_bracket> .




(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise go \<open>SE_Module_SDistr_a_cb_i\<close>*) 
lemma SE_Module_SDistr_a_dbc
      [where Cr'=True, \<phi>reason_template default %derived_SE_sdistr+1]:
  \<comment> \<open>Boundary situations (when c or d equals zero) are captured here, so the rule has a higher priority
      than \<open>SE_Module_SDistr_da_bc_nc_i\<close> and \<open>SE_Module_SDistr_ad_cb_nc_i\<close> in order to preempt the
      boundary situations.\<close>
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d b db c a)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (C\<^sub>c \<longrightarrow> Ds c \<and> Ds db) \<and> (C\<^sub>d \<longrightarrow> Ds d \<and> Ds b)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> x' : (fst (?\<^sub>s\<^sub>R C\<^sub>d (uz b d) (snd (?\<^sub>s\<^sub>L C\<^sub>c (uz c db) (fst x)))), snd x)
\<Longrightarrow> x' \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (C\<^sub>c \<longrightarrow> Dx c db (fst x)) \<and> (C\<^sub>d \<longrightarrow> Dx b d (snd (?\<^sub>s\<^sub>L C\<^sub>c (uz c db) (fst x))))
\<Longrightarrow> if Cw then class.ab_semigroup_mult ( (*) :: 'c option BI \<Rightarrow> 'c option BI \<Rightarrow> 'c option BI ) else True
\<Longrightarrow> ((snd y, snd (?\<^sub>s\<^sub>R C\<^sub>d (uz b d) (snd (?\<^sub>s\<^sub>L C\<^sub>c (uz c db) (fst x)))), fst (?\<^sub>s\<^sub>L C\<^sub>c (uz c db) (fst x))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c)
      = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [unfolded equation\<^sub>3\<^sub>1_cond_def, simp] and SU[] and _ and _ and _ and Tr and _ and IF[] and b
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_LCond_\<phi>Some[OF SU, where s=\<open>db\<close> and t=c and r=a and C=C\<^sub>c]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_RCond_\<phi>Some[OF SU, where s=\<open>d\<close> and t=b and r=db and C=C\<^sub>d]
    apply_rule swap_\<phi>Cond_Ins_by_raw_class[OF IF, THEN eq_right_frame, THEN eq_right_frame]
    apply_rule swap_\<phi>Cond_Ins_by_raw_class[OF IF, THEN eq_right_frame]
    Tr
    apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F\<^sub>3 b\<close>]]
  \<medium_right_bracket> .


(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Module_SDistr_da_b_i\<close> *)
lemma SE_Module_SDistr_dac_b
      [\<phi>reason_template default %derived_SE_sdistr+1]:
  \<comment> \<open>Boundary situations (when c or d equals zero) are captured here, so the rule has a higher priority
      than \<open>SE_Module_SDistr_da_bc_nc_i\<close> and \<open>SE_Module_SDistr_ad_cb_nc_i\<close> in order to preempt the
      boundary situations.\<close>
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d a da c b)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (C\<^sub>d \<longrightarrow> Ds d \<and> Ds a) \<and> (C\<^sub>c \<longrightarrow> Ds da \<and> Ds c)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (C\<^sub>d \<longrightarrow> Dx a d (fst x, x\<^sub>d)) \<and>
           (C\<^sub>c \<longrightarrow> Dx c da (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (fst x, x\<^sub>d)))
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> x' : (?\<^sub>j\<^sub>L C\<^sub>c (z c da) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d  (z a d) (fst x, x\<^sub>d)), w)
\<Longrightarrow> x' \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, x\<^sub>c, w) \<Ztypecolon> \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr;
         simp add: Cond_\<phi>Prod_expn_\<phi>Some \<phi>Prod_expn'')
  \<medium_left_bracket> premises A[unfolded equation\<^sub>3\<^sub>1_cond_def, simp] and _ and _ and _ and _ and _ and Tr and _
    note \<phi>Some_\<phi>Prod[symmetric, simp] ;;
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_RCond_\<phi>Some[where s=d and t=a and F=F\<^sub>1 and r=da and x=\<open>(fst x, x\<^sub>d)\<close> and C=C\<^sub>d]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_LCond_\<phi>Some[where s=da and t=c and F=F\<^sub>1 and x=\<open>(x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d  (z a d) (fst x, x\<^sub>d))\<close> and C=C\<^sub>c]
    Tr
  \<medium_right_bracket> .

(*

lemma SE_Module_SDistr_dac_b_nc_i
      [\<phi>reason_template default %derived_SE_sdistr_noncomm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id d + id a + id c = id b @action \<A>arith_eq)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F\<^sub>1 Ds Dx z Dx' z'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds (d + a) \<and> Ds c \<and> d + a ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, x\<^sub>d) \<and> Dx' (d + a) c (z a d (fst x, x\<^sub>d), x\<^sub>c)
\<Longrightarrow> (z' (d + a) c (z a d (fst x, x\<^sub>d), x\<^sub>c), w) \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>1 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, x\<^sub>c, w) \<Ztypecolon> \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[True] F\<^sub>1 c \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for R :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr;
         simp add: Cond_\<phi>Prod_expn_\<phi>Some \<phi>Prod_expn'')
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and _ and Tr and _
    note \<phi>Some_\<phi>Prod[symmetric, simp] ;;
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where s=d and t=a and F=F\<^sub>1 and x=\<open>(fst x, x\<^sub>d)\<close>]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev_\<phi>Some[where s=\<open>d+a\<close> and t=c and F=F\<^sub>1 and x=\<open>(z a d (fst x, x\<^sub>d), x\<^sub>c)\<close>]
    Tr
  \<medium_right_bracket> .

*)

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative separation algebra. d \<noteq> 0
   All problems on semimodules of commutative scalars (and associative separation algebra) reduces to
    \<open>SE_Module_SDistr_da_b_i\<close> and \<open>SE_Module_SDistr_a_cb_i\<close>
*)
lemma SE_Module_SDistr_da_b_i
      [where Cw'=True, \<phi>reason_template default %derived_SE_sdistr_comm_no_adz]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 d a b)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx' z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx' a d (fst x, x\<^sub>d)
\<Longrightarrow> (z a d (fst x, x\<^sub>d), w) \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def equation\<^sub>2\<^sub>1_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F\<^sub>1 and x=\<open>(fst x, x\<^sub>d)\<close>]
       Tr
  \<medium_right_bracket> .


(*
(* [--------a---------]
   [-----b-----][--c--]
   Give a, expect b; Remain c, d = 0.
   c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Module_SDistr_a_cb_i\<close>*)
lemma SE_Module_SDistr_a_bc_i
  [where Cr'=True, \<phi>reason_template default %derived_SE_sdistr_comm_no_adz pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a = id b + id c @action \<A>arith_eq)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx' uz'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S_rev F\<^sub>1 Dx' uz' Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds b \<and> Ds c \<and> b ##\<^sub>+ c
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> (fst (uz b c (fst x)), snd x) \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> ((snd (uz b c (fst x)), snd y) \<Ztypecolon> \<half_blkcirc>[True] F\<^sub>1 c \<^emph> \<half_blkcirc>[Cr] R) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_ab_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises a and SD\<^sub>U[] and SD\<^sub>U_rev[] and _ and _ and _ and Tr and b
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_rev_\<phi>Some[where t=c and s=b and F=F\<^sub>1, OF SD\<^sub>U SD\<^sub>U_rev]
    Tr
    b
  \<medium_right_bracket> .
*)

(* [-----a-----][--d--]
   [--------b---------]
   Give a, expect b; Need d, c = 0.
   Also covers non-commutative separation algebra.
   d \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Module_SDistr_da_b_i\<close>
*)
(*
lemma SE_Module_SDistr_ad_b_i
      [where Cw' = True, \<phi>reason_template default %derived_SE_sdistr_comm_no_adz pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> id a + id d = id b @action \<A>arith_eq)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx' uz'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F\<^sub>1 Ds Dx' uz' Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> a ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d (fst x, x\<^sub>d)
\<Longrightarrow> (uz a d (fst x, x\<^sub>d), w) \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> (snd x \<Ztypecolon> \<half_blkcirc>[Cw'] W') = ((x\<^sub>d, w) \<Ztypecolon> \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[Cw] W) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw'] W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises [simp] and SD\<^sub>Z[] and SD\<^sub>Z_rev[] and _ and _ and _ and Tr and [simp]
    note \<phi>Prod_expn''[simp] \<phi>Prod_expn'[simp]
    ;; apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_rev_\<phi>Some[where s=a and t=d and F=F\<^sub>1 and x=\<open>(fst x, x\<^sub>d)\<close>, OF SD\<^sub>Z SD\<^sub>Z_rev]
       Tr
  \<medium_right_bracket> .
*)


(* [---------a--------]
   [--c--][-----b-----]
   Give a, expect b; Remain c, d = 0. c \<noteq> 0
   All problems on semimodules of commutative scalars (and associative separation algebra) reduces to
    \<open>SE_Module_SDistr_da_b\<close> and \<open>SE_Module_SDistr_a_cb\<close>
*)
lemma SE_Module_SDistr_a_cb[\<phi>reason_template default %derived_SE_sdistr_comm_no_adz]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 c b a)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> (fst (uz b c (fst x)), snd x) \<Ztypecolon> F\<^sub>1 b \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> if Cw then class.ab_semigroup_mult ( (*) :: 'c option BI \<Rightarrow> 'c option BI \<Rightarrow> 'c option BI ) else True
\<Longrightarrow> ((snd y, snd (uz b c (fst x))) \<Ztypecolon> \<half_blkcirc>[Cr] R \<^emph> \<half_blkcirc>[True] F\<^sub>1 c) = (r \<Ztypecolon> \<half_blkcirc>[Cr'] R') @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> F\<^sub>1 a \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y, r) \<Ztypecolon> F\<^sub>3 b \<^emph>[Cr'] R' \<w>\<i>\<t>\<h> P \<close>
  for W :: \<open>('c::sep_semigroup,'d) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def equation\<^sub>2\<^sub>1_def
  apply (simp add: cond_prod_transformation_rewr; simp add:  Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises A and _ and _ and _ and _ and Tr and IF[] and b
    note \<phi>Prod_expn'' [simp] A[THEN conjunct2, simp] ;;
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[where t=b and s=c and F=F\<^sub>1, unfolded A[THEN conjunct1]]
    apply_rule swap_\<phi>Cond_Ins_by_raw_class[OF IF, THEN eq_right_frame]
    Tr
    apply_rule b[THEN eq_right_frame[where R=\<open>fst y \<Ztypecolon> \<black_circle> F\<^sub>3 b\<close>]]
  \<medium_right_bracket> .


(*
context
  fixes F\<^sub>1 :: \<open>'a::partial_add_magma \<Rightarrow> ('e, 'b) \<phi> \<Rightarrow> ('c::sep_ab_semigroup, 'f) \<phi>\<close>
    and F\<^sub>3 :: \<open>'a \<Rightarrow> ('g\<^sub>c, 'g\<^sub>x) \<phi> \<Rightarrow> ('c, 'h) \<phi>\<close>
    and a b :: 'a
    and T :: \<open>('e, 'b) \<phi>\<close>
    and U :: \<open>('g\<^sub>c, 'g\<^sub>x) \<phi>\<close>
begin

lemmas SE_Module_SDistr_da_bc_i__lift_src
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_src\<^sub>R[where F=F\<^sub>1 and one=a and T=T,
                             OF _ SE_Module_SDistr_da_bc_i[where F\<^sub>1=F\<^sub>1 and a=a and T=T]]

lemmas SE_Module_SDistr_da_bc_i__lift_tgt
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_tgt\<^sub>R[where F=F\<^sub>3 and one=b and T=U,
                             OF _ SE_Module_SDistr_da_bc_i[where F\<^sub>3=F\<^sub>3 and b=b and U=U]]

lemmas SE_Module_SDistr_ad_cb_i__lift_src
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_src\<^sub>R[where F=F\<^sub>1 and one=a and T=T,
                             OF _ SE_Module_SDistr_ad_cb_i[where F\<^sub>1=F\<^sub>1 and a=a and T=T]]

lemmas SE_Module_SDistr_ad_cb_i__lift_tgt
  = Semimodule_One_lift_tgt\<^sub>R[where F=F\<^sub>3 and one=b and T=U,
                             OF _ SE_Module_SDistr_ad_cb_i[where F\<^sub>3=F\<^sub>3 and b=b and U=U]]

lemmas SE_Module_SDistr_a_dbc_i__lift_src
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_src\<^sub>R[where F=F\<^sub>1 and one=a and T=T,
                             OF _ SE_Module_SDistr_a_dbc_i[where F\<^sub>1=F\<^sub>1 and a=a and T=T]]

lemmas SE_Module_SDistr_a_dbc_i__lift_tgt
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_tgt\<^sub>R[where F=F\<^sub>3 and one=b and T=U,
                             OF _ SE_Module_SDistr_a_dbc_i[where F\<^sub>3=F\<^sub>3 and b=b and U=U]]

lemmas SE_Module_SDistr_dac_b_i__lift_src
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_src\<^sub>R[where F=F\<^sub>1 and one=a and T=T,
                             OF _ SE_Module_SDistr_dac_b_i[where F\<^sub>1=F\<^sub>1 and a=a and T=T]]

lemmas SE_Module_SDistr_dac_b_i__lift_tgt
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_tgt\<^sub>R[where F=F\<^sub>3 and one=b and T=U,
                             OF _ SE_Module_SDistr_dac_b_i[where F\<^sub>3=F\<^sub>3 and b=b and U=U]]

lemmas SE_Module_SDistr_da_b_i__lift_src
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_src\<^sub>R[where F=F\<^sub>1 and one=a and T=T,
                             OF _ SE_Module_SDistr_da_b_i[where F\<^sub>1=F\<^sub>1 and a=a and T=T]]

lemmas SE_Module_SDistr_da_b_i__lift_tgt
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_tgt\<^sub>R[where F=F\<^sub>3 and one=b and T=U,
                             OF _ SE_Module_SDistr_da_b_i[where F\<^sub>3=F\<^sub>3 and b=b and U=U]]

lemmas SE_Module_SDistr_a_bc_i__lift_src
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_src\<^sub>R[where F=F\<^sub>1 and one=a and T=T,
                             OF _ SE_Module_SDistr_a_bc_i[where F\<^sub>1=F\<^sub>1 and a=a and T=T]]

lemmas SE_Module_SDistr_a_bc_i__lift_tgt
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_tgt\<^sub>R[where F=F\<^sub>3 and one=b and T=U,
                             OF _ SE_Module_SDistr_a_bc_i[where F\<^sub>3=F\<^sub>3 and b=b and U=U]]

lemmas SE_Module_SDistr_ad_b_i__lift_src
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_src\<^sub>R[where F=F\<^sub>1 and one=a and T=T,
                             OF _ SE_Module_SDistr_ad_b_i[where F\<^sub>1=F\<^sub>1 and a=a and T=T]]

lemmas SE_Module_SDistr_ad_b_i__lift_tgt
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_tgt\<^sub>R[where F=F\<^sub>3 and one=b and T=U,
                             OF _ SE_Module_SDistr_ad_b_i[where F\<^sub>3=F\<^sub>3 and b=b and U=U]]

lemmas SE_Module_SDistr_a_cb_i__lift_src
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_src\<^sub>R[where F=F\<^sub>1 and one=a and T=T,
                             OF _ SE_Module_SDistr_a_cb_i[where F\<^sub>1=F\<^sub>1 and a=a and T=T]]

lemmas SE_Module_SDistr_a_cb_i__lift_tgt
       [\<phi>reason_template default %derived_SE_sdistr_comm pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]
  = Semimodule_One_lift_tgt\<^sub>R[where F=F\<^sub>3 and one=b and T=U,
                             OF _ SE_Module_SDistr_a_cb_i[where F\<^sub>3=F\<^sub>3 and b=b and U=U]]

end
*)

(*Done*)

(* [-----a-----][--d--]
   [--c--][-----b-----]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to either
             \<open>SE_Module_SDistr_da_b_i\<close> or \<open>SE_Module_SDistr_a_cb_i\<close>
*)


(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Module_SDistr_da_b_i\<close>
*)


(* [--d--][--a--][--c--]
   [---------b---------]
   Give a, expect b, need d, c.
   d, c \<noteq> 0; scalar has to be non-commutative; otherwise reduces to \<open>SE_Module_SDistr_a_cb_i\<close>
*)


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
lemma SE_Module_SDistr_da_b_na[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b @action \<A>arith_eq
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
lemma SE_Module_SDistr_ad_b_na[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = b @action \<A>arith_eq
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
lemma SE_Module_SDistr_dac_b_nc_na_W[\<phi>reason_template 38]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a + c = b @action \<A>arith_eq
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
lemma SE_Module_SDistr_da_b_na_W[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> d + a = b @action \<A>arith_eq
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
lemma SE_Module_SDistr_ad_b_na_W[\<phi>reason_template 36]:
  \<open> \<g>\<u>\<a>\<r>\<d> a + d = b @action \<A>arith_eq
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

lemma SE_Module_SDistr_a_cb_noassoc[\<phi>reason_template default %derived_SE_sdistr_noassoc]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 c b a)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b c (fst x)
\<Longrightarrow> fst (uz b c (fst x)) \<Ztypecolon> F1 b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, snd (uz b c (fst x))) \<Ztypecolon> F3 b \<^emph>[True] F1 c \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def equation\<^sub>2\<^sub>1_def
  \<medium_left_bracket> premises A[simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S[where s=\<open>c\<close> and t=b and F=F1, unfolded A[THEN conjunct1]]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
   d \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Module_SDistr_a_cb_noassoc\<close>
*)
lemma SE_Module_SDistr_a_bd_Tr
      [\<phi>reason_template default %derived_SE_sdistr_noassoc pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 b d a)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F1 Ds Dx\<^sub>o uz\<^sub>o
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S_rev F1 Dx\<^sub>o uz\<^sub>o Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b d (fst x)
\<Longrightarrow> fst (uz b d (fst x)) \<Ztypecolon> F1 b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, snd (uz b d (fst x))) \<Ztypecolon> F3 b \<^emph>[True] F1 d \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def equation\<^sub>2\<^sub>1_def
  \<medium_left_bracket> premises A[simp] and SD\<^sub>U[] and SD\<^sub>U_rev[] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_rev[where s=\<open>b\<close> and t=d and F=F1, OF SD\<^sub>U SD\<^sub>U_rev, unfolded A[THEN conjunct1]]
    Tr
  \<medium_right_bracket> .

(* [--d--][-----a-----]
   [---------b--------]
   Give a, expect b, remain d. c \<noteq> 0
*)
lemma SE_Module_SDistr_da_b_noassoc[\<phi>reason_template default %derived_SE_sdistr_noassoc]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 d a b)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d x
\<Longrightarrow> z a d x \<Ztypecolon> F1 b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a \<^emph>[True] F1 d \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, unspec) \<Ztypecolon> F3 b \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def equation\<^sub>2\<^sub>1_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z[where s=\<open>d\<close> and t=a and F=F1]
    Tr
  \<medium_right_bracket> .

(* [-----a-----][--d--]
   [---------b--------]
   Give a, expect b, remain d.
   d \<noteq> 0; scalar has to be non-commutative; otherwise go to \<open>SE_Module_SDistr_da_b_noassoc\<close>
*)
lemma SE_Module_SDistr_ad_b_noassoc
      [\<phi>reason_template default %derived_SE_sdistr_noassoc pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 a d b)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F1 Ds Dx\<^sub>o z\<^sub>o
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z_rev F1 Ds Dx\<^sub>o z\<^sub>o Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F1 F3
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx a d x
\<Longrightarrow> z a d x \<Ztypecolon> F1 b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a \<^emph>[True] F1 d \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, unspec) \<Ztypecolon> F3 b \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def id_apply NO_SIMP_def equation\<^sub>2\<^sub>1_def
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
lemma SE_Module_SDistr_a_db_Tr[\<phi>reason_template default %derived_SE_sdistr_noassoc]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = c + b @action \<A>arith_eq
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds b \<and> c ##\<^sub>+ b
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx c b x
\<Longrightarrow> fst (uz c b x) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] snd (uz c b x) \<Ztypecolon> F1 c T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S[where s=\<open>c\<close> and t=b and F=F1]
    Tr
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
*)
lemma SE_Module_SDistr_a_bd_Tr[\<phi>reason_template default %derived_SE_sdistr_noassoc]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + d @action \<A>arith_eq
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S_rev F1 T Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul F1 F3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b \<and> b ##\<^sub>+ d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Dx b d x
\<Longrightarrow> fst (uz b d x) \<Ztypecolon> F1 b T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> F1 a T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F3 b U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] snd (uz b d x) \<Ztypecolon> F1 d T \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def
  \<medium_left_bracket> premises [simp] and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_rev[where s=\<open>b\<close> and t=d and F=F1]
    Tr
  \<medium_right_bracket> .

paragraph \<open>Assuming associativity, allowing remainders\<close>

subparagraph \<open>Has Additive Zero\<close>

(* [---------a---------]
   [--d--][--b--][--c--]
   Give a, expect b, remain d, c. *) 
lemma SE_Module_SDistr_a_dbc_Tr_R[\<phi>reason_template 33]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b + c @action \<A>arith_eq
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F1 T Ds Dx uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S_rev F1 T Ds Dx' uz'
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
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_rev[where s=\<open>d + b\<close> and t=c and F=F1, folded a]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S[where s=\<open>d\<close> and t=b and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

subparagraph \<open>No Additive Zero\<close>

(* [---------a--------]
   [--d--][-----b-----]
   Give a, expect b, remain d.
   Assuming associativity, allow R
*)
lemma SE_Module_SDistr_a_db_Tr_R[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = d + b @action \<A>arith_eq
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F1 T Ds Dx uz
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
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S[where s=\<open>d\<close> and t=b and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

(* [---------a--------]
   [-----b-----][--d--]
   Give a, expect b, remain d.
   Assuming associativity, allow R
*)
lemma SE_Module_SDistr_a_bd_Tr_R[\<phi>reason_template 32]:
  \<open> \<g>\<u>\<a>\<r>\<d> a = b + d @action \<A>arith_eq
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S_rev F1 T Ds Dx uz
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
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_rev[where s=\<open>b\<close> and t=d and F=F1]
    Tr
    apply_rule C'[THEN eq_right_frame[where R=\<open>y \<Ztypecolon> F3 b U\<close>]]
  \<medium_right_bracket> .

(*DONE*)

(*The dual of the above rules is \<A>SEa*)
*)

subsection \<open>ToA mapper over Semimodules\<close>

context notes prod_opr_norm[simp] \<phi>Prod_expn''[simp] comp_assoc[symmetric, simp]
begin

(* [--d--][-----a-----]
   [-----b-----][--c--]
   Give a, expect b; Need d, remain c.
   d, c \<noteq> 0; the scalar has to be non-commutative, otherwise reduces to either \<open>SE_Module_SDistr_da_b_i\<close> or \<open>SE_Module_SDistr_a_cb_i\<close>
   as we assume non-commutative scalar, the concrete algebra must be commutative*)

lemma SE_Module_SDistr_da_bc_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri
          name F\<^sub>1.module_mapper\<^sub>d\<^sub>a\<^sub>_\<^sub>b\<^sub>c
          pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<comment> \<open>idk which one would be better. I perfer the former because,
      the getters are essentially identical, but the domain of the premises is simpler in the former\<close>
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> dabc_equation d a b c)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx\<^sub>u uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx\<^sub>z z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1' Ds' Dx\<^sub>u' uz'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1' Ds' Dx\<^sub>z' z'
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> Ds b \<and> Ds c \<and> Ds' b \<and> Ds' c \<and> Ds' d \<and> Ds' a
\<comment> \<open>TODO: \<open>module_mapper\<^sub>2\<^sub>2 True d a b c uz' z' uz z Dx' Dx\<^sub>u' Dx Dx\<^sub>u D\<^sub>M f\<^sub>c f\<^sub>b f\<^sub>a f\<^sub>d\<close>\<close>

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>(x\<^sub>a,w,x\<^sub>d)\<in>D. let (y\<^sub>c, y) = uz c b (z a d (x\<^sub>a,x\<^sub>d))
                           in D\<^sub>s\<^sub>z (x\<^sub>a,x\<^sub>d) (f\<^sub>c y\<^sub>c, f\<^sub>b y) \<and>
                              Dx\<^sub>z a d (x\<^sub>a,x\<^sub>d) \<and>
                              Dx\<^sub>u c b (z a d (x\<^sub>a,x\<^sub>d)) \<and>
                              Dx\<^sub>z' c b (f\<^sub>c y\<^sub>c, f\<^sub>b y) \<and>
                              Dx\<^sub>u' a d (z' c b (f\<^sub>c y\<^sub>c, f\<^sub>b y)) )

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f\<^sub>b \<otimes>\<^sub>f w : F\<^sub>1 b \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1' b \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x\<^sub>a,w,x\<^sub>d). case uz c b (z a d (x\<^sub>a,x\<^sub>d)) of (x\<^sub>c,x\<^sub>b) \<Rightarrow> (x\<^sub>b,w)) ` D

\<Longrightarrow> separatable_module_zip True d a b c uz' z' uz z D\<^sub>s\<^sub>z f\<^sub>c f\<^sub>b f\<^sub>a f\<^sub>d @action \<A>_template_reason undefined

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f (r \<otimes>\<^sub>f f\<^sub>c) : F\<^sub>3 b \<^emph>[True] (R [C\<^sub>R]\<^emph> F\<^sub>1 c) \<mapsto> F\<^sub>3' b \<^emph>[True] (R' [C\<^sub>R]\<^emph> F\<^sub>1' c)
    \<o>\<v>\<e>\<r> f\<^sub>a \<otimes>\<^sub>f w \<otimes>\<^sub>f f\<^sub>d : F\<^sub>1 a \<^emph>[True] (W [C\<^sub>W]\<^emph> F\<^sub>1 d) \<mapsto> F\<^sub>1' a \<^emph>[True] (W' [C\<^sub>W]\<^emph> F\<^sub>1' d)
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x\<^sub>a,w,x\<^sub>d). let (x\<^sub>c,x\<^sub>b) = uz c b (z a d (x\<^sub>a,x\<^sub>d))
                                 ; (y,r) = h (x\<^sub>b,w)
                                in (y,r,x\<^sub>c))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(y,r,x\<^sub>c). let (x\<^sub>b,w) = s (y,r)
                                 ; (x\<^sub>a,x\<^sub>d) = uz' a d (z' c b (x\<^sub>c,x\<^sub>b))
                                in (x\<^sub>a,w,x\<^sub>d))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises A[THEN dabc_equation_D_main, simp] and _ and _ and _ and _ and _ and _ and Tr
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=a and s=d and F=F\<^sub>1 and x=\<open>case x of (x\<^sub>a,w,x\<^sub>d) \<Rightarrow> (x\<^sub>a,x\<^sub>d)\<close>]
    certified by (insert useful(1) useful(2)[THEN bspec[OF _ \<open>x \<in> D\<close>]],
                  clarsimp split: prod.split simp add: useful(3-)) ;;
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[where t=c and s=b and F=F\<^sub>1]
    certified by (insert useful(1) useful(2)[THEN bspec[OF _ \<open>x \<in> D\<close>]],
                  clarsimp split: prod.split simp add: useful(3-)) ;;
    apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>case x of (x\<^sub>a,w,x\<^sub>d) \<Rightarrow> case uz c b (z a d (x\<^sub>a,x\<^sub>d)) of (x\<^sub>c,x\<^sub>b) \<Rightarrow> (x\<^sub>b,w)\<close>]
      certified by (clarsimp split: prod.split simp add: \<phi> image_iff, insert \<phi>(4), force)
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply(rule conjunctionI, rule)
  \<medium_left_bracket> premises A[THEN dabc_equation_D_main] and _ and _ and _ and _ and _ and _ and Tr
    note A[THEN conjunct1, symmetric, simp]
         A[THEN conjunct2, simp] ;;
    apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>case x of (y,r,x\<^sub>c) \<Rightarrow> (y,r)\<close>]
      certified by (insert useful(1), clarsimp split: prod.split simp add: \<phi> image_iff,
                    case_tac \<open>uz c b (z a d (aa, ba))\<close>, clarsimp,
                    case_tac \<open>h (bb, aaa)\<close>, clarsimp, force) ;;
    
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=c and s=b and F=F\<^sub>1' and x=\<open>case x of (y,r,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (x\<^sub>c,x\<^sub>b)\<close>]
    certified apply (insert useful(1), simp add: image_iff del: split_paired_All, elim bexE)
              subgoal premises prems for y
                by (insert prems(2) useful(2)[THEN bspec[OF _ prems(1)]]
                             ToA_Mapper_f_expn[OF Tr, simplified, THEN bspec[OF _ prems(1)], symmetric],
                    clarsimp simp add: prod.rotL_def useful(3-) split: prod.split) . ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[where t=a and s=d and F=F\<^sub>1' and x=\<open>case x of (y,r,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> z' c b (x\<^sub>c,x\<^sub>b)\<close>]
    certified apply (insert useful(1), simp add: image_iff del: split_paired_All, elim bexE)
              subgoal premises prems for y
                by (insert prems(2) useful(2)[THEN bspec[OF _ prems(1)]]
                             ToA_Mapper_f_expn[OF Tr, simplified, THEN bspec[OF _ prems(1)], symmetric],
                    clarsimp simp add: prod.rotL_def useful(3-) split: prod.split) . 

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, unfold Premise_def conj_imp_eq_imp_imp, rule ballI)
    subgoal premises prems for x proof -
      show ?thesis
        by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f\<^sub>b \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                     simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                      \<open>separatable_module_zip _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>
                            [unfolded separatable_module_zip_def, THEN spec[where x=\<open>case x of (x\<^sub>a,w,x\<^sub>d) \<Rightarrow> (x\<^sub>a,x\<^sub>d)\<close>]],
            clarsimp split: prod.split simp: \<open>dabc_equation d a b c\<close>,
            insert prems(14) prems(17), fastforce)
    qed .



lemma SE_Module_SDistr_ad_cb_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri
          name F\<^sub>1.module_mapper\<^sub>a\<^sub>d\<^sub>_\<^sub>c\<^sub>b
          pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> dabc_equation c b a d)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx\<^sub>u uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>3 F\<^sub>3'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx\<^sub>z z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1' Ds' Dx\<^sub>u' uz'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1' Ds' Dx\<^sub>z' z'
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds d \<and> Ds c \<and> Ds b \<and> Ds' c \<and> Ds' b \<and> Ds' a \<and> Ds' d
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. let (x\<^sub>a,w,x\<^sub>d) = x
                    ; (x\<^sub>b,x\<^sub>c) = uz b c (z d a (x\<^sub>d,x\<^sub>a))
                   in D\<^sub>s\<^sub>z (x\<^sub>d,x\<^sub>a) (f x\<^sub>b, f\<^sub>c x\<^sub>c) \<and>
                      Dx\<^sub>z d a (x\<^sub>d,x\<^sub>a) \<and>
                      Dx\<^sub>u b c (z d a (x\<^sub>d,x\<^sub>a)) \<and>
                      Dx\<^sub>z' b c (f x\<^sub>b, f\<^sub>c x\<^sub>c) \<and>
                      Dx\<^sub>u' d a (z' b c (f x\<^sub>b, f\<^sub>c x\<^sub>c)) )

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 b \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1' b \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x\<^sub>a,w,x\<^sub>d). let (x\<^sub>b,x\<^sub>c) = uz b c (z d a (x\<^sub>d,x\<^sub>a)) in (x\<^sub>b,w)) ` D

\<Longrightarrow> separatable_module_zip False a d c b uz' z' uz z D\<^sub>s\<^sub>z f f\<^sub>c f\<^sub>d f' @action \<A>_template_reason undefined

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f (r \<otimes>\<^sub>f f\<^sub>c) : F\<^sub>3 b \<^emph>[True] (R [C\<^sub>R]\<^emph> F\<^sub>1 c) \<mapsto> F\<^sub>3' b \<^emph>[True] (R' [C\<^sub>R]\<^emph> F\<^sub>1' c)
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w \<otimes>\<^sub>f f\<^sub>d : F\<^sub>1 a \<^emph>[True] (W [C\<^sub>W]\<^emph> F\<^sub>1 d) \<mapsto> F\<^sub>1' a \<^emph>[True] (W' [C\<^sub>W]\<^emph> F\<^sub>1' d)
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x\<^sub>a,w,x\<^sub>d). let (x\<^sub>b,x\<^sub>c) = uz b c (z d a (x\<^sub>d,x\<^sub>a))
                                 ; (y,r) = h (x\<^sub>b,w)
                                in (y,r,x\<^sub>c))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(y,r,x\<^sub>c). let (x\<^sub>b,w) = s (y,r)
                                 ; (x\<^sub>d,x\<^sub>a) = uz' d a (z' b c (x\<^sub>b,x\<^sub>c))
                                in (x\<^sub>a,w,x\<^sub>d))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def SIMP_def
            Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin conj_imp_eq_imp_imp;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises dabc[THEN dabc_equation_D_main] and _ and _ and _ and _ and _ and _ and Tr and _ 
    note dabc[THEN conjunct1, symmetric, simp]
         dabc[THEN conjunct2, simp]
    note [[\<phi>trace_reasoning = 2]];;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=d and s=a and F=F\<^sub>1]
      certified by (of_tac \<open>(snd (snd x), fst x)\<close>, clarsimp split: prod.split simp add: useful, insert useful(1,2), force) ;;
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[where t=b and s=c and F=F\<^sub>1]
    apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>case x of (x\<^sub>a,w,x\<^sub>d) \<Rightarrow> case uz b c (z d a (x\<^sub>d,x\<^sub>a)) of (x\<^sub>b,x\<^sub>c) \<Rightarrow> (x\<^sub>b,w)\<close>]
      certified by (clarsimp split: prod.split simp add: useful)
  \<medium_right_bracket> certified by (clarsimp split: prod.split simp add: useful)
    apply(rule conjunctionI, rule)
  \<medium_left_bracket> premises dabc[THEN dabc_equation_D_main, simp] and _ and _ and _ and _ and _ and _ and Tr

    apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>case x of (y,r,x\<^sub>c) \<Rightarrow> (y,r)\<close>]
    certified apply (clarsimp simp add: image_iff useful split: prod.split,
                     insert useful(1), clarsimp simp add: image_iff split: prod.split)
              subgoal premises prems for x1 aa ba ab ac bb
                by (rule bexI[OF _ prems(2)], insert prems(1,3), clarsimp, case_tac \<open>h (x1a, ac)\<close>, clarsimp) . ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[where t=b and s=c and F=F\<^sub>1' and x=\<open>case x of (y,r,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (x\<^sub>b,x\<^sub>c)\<close>]
    certified apply (insert useful(1)[simplified image_image], simp add: image_iff del: split_paired_All, elim bexE)
              subgoal premises prems for y
                by (insert prems(2) useful(2)[THEN bspec[OF _ prems(1)]]
                    ToA_Mapper_f_expn[OF Tr, simplified, THEN bspec[OF _ prems(1)], symmetric],
                    clarsimp simp add: useful(4-) split: prod.split) . ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[where t=d and s=a and F=F\<^sub>1' and x=\<open>(z' b c o apfst (fst \<circ> s) \<circ> prod.rotL) x\<close>]
    certified apply (insert useful(1)[simplified image_image], simp add: image_iff del: split_paired_All, elim bexE)
              subgoal premises prems for y
                by (insert prems(2) useful(2)[THEN bspec[OF _ prems(1)]]
                    ToA_Mapper_f_expn[OF Tr, simplified, THEN bspec[OF _ prems(1)], symmetric],
                    clarsimp simp add: useful(3-) split: prod.split) .
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, unfold Premise_def conj_imp_eq_imp_imp, rule ballI)
    subgoal premises prems for x proof -

      show ?thesis
        by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                     simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                      \<open>separatable_module_zip _ _ _ _ _  _ _ _ _ _ _ _ _ _\<close>[unfolded separatable_module_zip_def, THEN spec[where x=\<open>case x of (x\<^sub>a,w,x\<^sub>d) \<Rightarrow> (x\<^sub>d,x\<^sub>a)\<close>]],
            clarsimp split: prod.split simp: \<open>dabc_equation c b a d\<close>,
            insert prems(14) prems(17), fastforce)
    qed .




text \<open>We present two redundant sets of rules for one identical function, where one uses conditional
  boolean flags to cover boundary cases using one rule and another uses specific rules to covers
  each boundary case. Expressions in the later form is simpler
  though the single rule in the former can be more flexible as it covers all cases.
  By default, we adopt the later form but we provide both of the rules
  to leave the choice to users.
 \<close>

lemma SE_Module_SDistr_a_dbc_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri
        name: F\<^sub>1.module_mapper\<^sub>a\<^sub>_\<^sub>d\<^sub>b\<^sub>c
        pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d b db c a)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds' Dx\<^sub>z z
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (C\<^sub>c \<longrightarrow> Ds c \<and> Ds db \<and> Ds' db \<and> Ds' c) \<and>
                  (C\<^sub>d \<longrightarrow> Ds d \<and> Ds b \<and> Ds' d \<and> Ds' b )
\<Longrightarrow> NO_SIMP (module_mapper\<^sub>3\<^sub>1\<^sub>C C\<^sub>c C\<^sub>d c b db d uz z Dx Dx\<^sub>z D\<^sub>G f\<^sub>c f f\<^sub>d f' getter)

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 b \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 b \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x,w). case getter x of (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)) ` D

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>G (fst x))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R  = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G  \<^emph> \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R' = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G' \<^emph> \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x,w). let (x\<^sub>c, x\<^sub>b, x\<^sub>d) = getter x
                              ; (y,r) = h (x\<^sub>b, w)
                             in (y, r, x\<^sub>d, x\<^sub>c))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(y,r,x\<^sub>d,x\<^sub>c). case s (y,r) of (x\<^sub>b,w) \<Rightarrow>
                        (?\<^sub>j\<^sub>L C\<^sub>c (z c db) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z b d) (x\<^sub>b,x\<^sub>d)), w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def module_mapper\<^sub>3\<^sub>1\<^sub>C_def
            Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises EC[unfolded equation\<^sub>3\<^sub>1_cond_def, simp] and SS[] and SZ[] and _
         and MG and Tr[] and D\<^sub>G[] and [] and [] and Dom[useful]
    note D\<^sub>G' = D\<^sub>G[THEN bspec[OF _ Dom]]
    note t1[useful] = MG[THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]] ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_LCond_\<phi>Some[OF SS, where s=\<open>db\<close> and t=c and C=C\<^sub>c]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_RCond_\<phi>Some[OF SS, where s=\<open>d\<close> and t=b and C=C\<^sub>d]

    apply_rule ToA_Mapper_onward[OF Tr,
        where x=\<open>case x of (x,w) \<Rightarrow> case ?\<^sub>s\<^sub>L C\<^sub>c (uz c db) x of (x\<^sub>c, x\<^sub>d\<^sub>b) \<Rightarrow> case ?\<^sub>s\<^sub>R C\<^sub>d (uz b d) x\<^sub>d\<^sub>b of (x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)\<close>]
      certified by (insert t1, clarsimp split: prod.split simp: image_iff, metis Dom fst_conv snd_conv)
      
  \<medium_right_bracket> certified by (insert t1, clarsimp simp add: image_iff split: prod.split)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises EC[unfolded equation\<^sub>3\<^sub>1_cond_def, simp] and SS[] and SZ[] and _
         and MG and Tr[] and D\<^sub>G and [] and [] and Dom'
    from Dom'
    obtain y where Dom[useful]: \<open>y \<in> D\<close>
               and x_def[simp]: \<open>x = (g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c) (case y of (x, w) \<Rightarrow>
                                              case getter x of (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<Rightarrow> case h (x\<^sub>b, w) of (y, r) \<Rightarrow> (y, r, x\<^sub>d, x\<^sub>c))\<close>
      by (clarsimp simp add: split_beta)
    note D\<^sub>G' = D\<^sub>G[THEN bspec[OF _ Dom]]
    note t1[useful] = MG[THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]] ;;

    apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apsnd fst x\<close>]
    certified by (insert t1 Dom, clarsimp simp add: image_iff split: prod.split, force) ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_RCond_\<phi>Some[OF SZ, where s=\<open>d\<close> and t=b and r=db and C=C\<^sub>d
                                                                and x=\<open>(apsnd fst \<circ> apfst (fst \<circ> s) \<circ> prod.rotL) x\<close>]
    certified by (insert useful(1) the_\<phi>(6) ToA_Mapper_f_expn_rev[OF Tr],
                  clarsimp simp add: image_iff \<open>C\<^sub>d \<longrightarrow> _ \<and> _\<close> split: prod.split, fastforce) ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_LCond_\<phi>Some[OF SZ, where s=\<open>db\<close> and t=c and r=a and C=C\<^sub>c
                                                             and x=\<open>case x of (y,r,x\<^sub>d,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z b d) (x\<^sub>b,x\<^sub>d))\<close>]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified, THEN bspec[OF _ Dom]],
          clarsimp simp add: image_iff split: prod.split, auto_sledgehammer)

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, unfold Premise_def conj_imp_eq_imp_imp, rule ballI)
    subgoal premises prems for x proof -

      show ?thesis
        by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                            simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                      \<open>\<forall>x. D\<^sub>G x \<longrightarrow> _\<close> [THEN spec[where x=\<open>fst x\<close>]],
            clarsimp split: prod.split, auto_sledgehammer)
    qed .


lemma SE_Module_SDistr_a_db_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri name F\<^sub>1.module_mapper\<^sub>a\<^sub>_\<^sub>d\<^sub>b]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 d b a)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds' Dx\<^sub>z z

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds b \<and> Ds' d \<and> Ds' b
\<Longrightarrow> module_mapper\<^sub>2\<^sub>1\<^sub>L b d uz z Dx Dx\<^sub>z D\<^sub>G f f\<^sub>d f'

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R\<^sub>G \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R\<^sub>G'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 b \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 b \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x,w). let (x\<^sub>b, x\<^sub>d) = uz b d x in (x\<^sub>b, w)) ` D

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>G (fst x))

\<Longrightarrow> if C\<^sub>W then class.ab_semigroup_mult ( (*) :: 'c option BI \<Rightarrow> 'c option BI \<Rightarrow> 'c option BI ) else True

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d : F\<^sub>3 b \<^emph>[True] (R\<^sub>G [C\<^sub>R]\<^emph> F\<^sub>1 d) \<mapsto> F\<^sub>3' b \<^emph>[True] (R\<^sub>G' [C\<^sub>R]\<^emph> F\<^sub>1 d)
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x,w). let (x\<^sub>b, x\<^sub>d) = uz b d x
                              ; (y,r) = h (x\<^sub>b, w)
                             in (y, r, x\<^sub>d))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(y,r,x\<^sub>d). case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (z b d (x\<^sub>b,x\<^sub>d), w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_semigroup_add \<Rightarrow> ('c::sep_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def module_mapper\<^sub>2\<^sub>1\<^sub>L_def
            Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric]
                   Cond_\<phi>Prod_expn_\<phi>Some LCond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises EC[unfolded equation\<^sub>2\<^sub>1_def] and SS[] and SZ[] and _
         and MG and Tr[] and D\<^sub>G[] and IF[] and Dom
    note D\<^sub>G' = D\<^sub>G[THEN bspec[OF _ Dom]]
    note t1[useful] = MG[THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]]
    note EC[THEN conjunct2, simp] ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where s=\<open>d\<close> and t=b, unfolded EC[THEN conjunct1]]
    apply_rule swap_\<phi>Cond_Ins_by_raw_class[OF IF, THEN eq_right_frame] ;;
    apply_rule ToA_Mapper_onward[OF Tr,
        where x=\<open>case x of (x,w) \<Rightarrow> case uz b d x of (x\<^sub>b,x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)\<close>]
      certified by (insert t1 Dom, clarsimp split: prod.split simp: image_iff, force)
  \<medium_right_bracket> certified by (clarsimp simp add: image_iff split: prod.split)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises EC[unfolded equation\<^sub>2\<^sub>1_def, simp] and SS[] and SZ[] and _
         and MG and Tr[] and D\<^sub>G[] and IF[] and Dom'[] 

    from Dom'
    obtain y where Dom[useful]: \<open>y \<in> D\<close>
               and x_def[simp]: \<open>x = (g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d) (case y of (x, w) \<Rightarrow> case uz b d x of (x\<^sub>b, x\<^sub>d) \<Rightarrow> case h (x\<^sub>b, w) of (y, r) \<Rightarrow> (y, r, x\<^sub>d))\<close>
      by (clarsimp simp add: split_beta)

    note D\<^sub>G' = D\<^sub>G[THEN bspec[OF _ Dom]]
    note t1[useful] = MG[THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]] ;;

    apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apsnd fst x\<close>]
    certified by (insert t1 Dom, clarsimp split: prod.split simp: image_iff, force) ;;

    apply_rule swap_\<phi>Cond_Ins_by_raw_class[OF IF, symmetric, THEN eq_right_frame]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ,
        where s=\<open>d\<close> and t=b and x=\<open>case x of (y,r,x\<^sub>d) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (x\<^sub>b,x\<^sub>d)\<close>]
      certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                    clarsimp split: prod.split simp: image_iff useful(4-)) ;;

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, unfold Premise_def conj_imp_eq_imp_imp, rule ballI)
    subgoal premises prems for x proof -
      show ?thesis
        by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                            simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                   \<open>\<forall>x. D\<^sub>G x \<longrightarrow> _\<close> [THEN spec[where x=\<open>fst x\<close>]],
            clarsimp split: prod.split, auto_sledgehammer)
    qed .



lemma SE_Module_SDistr_a_d\<epsilon>c_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri
        name: F\<^sub>1.module_mapper\<^sub>a\<^sub>_\<^sub>d\<^sub>\<epsilon>\<^sub>c
        pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d \<epsilon> d\<epsilon> c a )
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1' Ds' Dx\<^sub>z z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F\<^sub>1 U \<epsilon> D\<^sub>\<epsilon>\<^sub>E E\<^sub>\<epsilon> Any_P\<^sub>E
\<Longrightarrow> TERM Semimodule_One\<^sub>I F\<^sub>3 T \<epsilon> D\<^sub>\<epsilon>\<^sub>I\<^sub>T I\<^sub>\<epsilon>\<^sub>T Any_P\<^sub>I\<^sub>T
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F\<^sub>1' U' \<epsilon> D\<^sub>\<epsilon>\<^sub>I I\<^sub>\<epsilon> Any_P\<^sub>I
\<Longrightarrow> TERM Semimodule_One\<^sub>E F\<^sub>3' T' \<epsilon> D\<^sub>\<epsilon>\<^sub>E\<^sub>T E\<^sub>\<epsilon>\<^sub>T Any_P\<^sub>E\<^sub>T
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (C\<^sub>c \<longrightarrow> Ds c \<and> Ds d\<epsilon> \<and> Ds' d\<epsilon> \<and> Ds' c) \<and>
                  (C\<^sub>d \<longrightarrow> Ds d \<and> Ds \<epsilon> \<and> Ds' d \<and> Ds' \<epsilon>)
\<Longrightarrow> NO_SIMP (module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C C\<^sub>c C\<^sub>d c \<epsilon> d\<epsilon> d uz z E\<^sub>\<epsilon> I\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I Dx Dx\<^sub>z D\<^sub>G f\<^sub>c f f\<^sub>d f' getter)

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G \<mapsto> T' \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : U \<^emph>[C\<^sub>W] W \<mapsto> U' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x,w). case getter x of (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)) ` D

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>G (fst x))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R  = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G  \<^emph> \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R' = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G' \<^emph> \<half_blkcirc>[C\<^sub>d] F\<^sub>1' d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1' c @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c : T \<^emph>[C\<^sub>R] R \<mapsto> T' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1' a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x,w). let (x\<^sub>c, x\<^sub>b, x\<^sub>d) = getter x
                              ; (y,r) = h (x\<^sub>b, w)
                             in (y, r, x\<^sub>d, x\<^sub>c))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(y,r,x\<^sub>d,x\<^sub>c). case s (y,r) of (x\<^sub>b,w) \<Rightarrow>
                        (?\<^sub>j\<^sub>L C\<^sub>c (z c d\<epsilon>) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z \<epsilon> d) (I\<^sub>\<epsilon> x\<^sub>b,x\<^sub>d)), w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
            Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def module_mapper\<^sub>3\<^sub>\<epsilon>\<^sub>C_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises EC[unfolded equation\<^sub>3\<^sub>1_cond_def, simp] and SS[] and SZ[] and S1\<^sub>E[] and [] and S1\<^sub>I[] and [] and _
         and MG and Tr[] and D\<^sub>G[] and [] and [] and Dom[useful]
    note D\<^sub>G' = D\<^sub>G[THEN bspec[OF _ Dom]]
    from EC have db: \<open>?\<^sub>+ True d\<epsilon> = ?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True \<epsilon> \<and> (C\<^sub>c \<longrightarrow> d\<epsilon> ##\<^sub>+ c) \<and> (C\<^sub>d \<longrightarrow> d ##\<^sub>+ \<epsilon>)\<close> by blast
    note t1[useful] = MG[THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF db] ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_LCond_\<phi>Some[OF SS, where s=\<open>d\<epsilon>\<close> and t=c and C=C\<^sub>c]
    
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_RCond_\<phi>Some[OF SS, where s=\<open>d\<close> and t=\<epsilon> and C=C\<^sub>d]

    apply_rule apply_Semimodule_One\<^sub>E_\<phi>Some[OF S1\<^sub>E] ;;

    apply_rule ToA_Mapper_onward[OF Tr,
        where x=\<open>case x of (x,w) \<Rightarrow> case getter x of (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)\<close>]
      certified by (insert t1 Dom, clarsimp split: prod.split simp: image_iff Let_def, auto_sledgehammer)

  \<medium_right_bracket> certified by (insert t1 Dom, clarsimp split: prod.split simp: image_iff Let_def, auto_sledgehammer)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises EC[unfolded equation\<^sub>3\<^sub>1_cond_def, simp] and SS[] and SZ[] and S1\<^sub>E[] and [] and S1\<^sub>I[] and [] and _
         and MG and Tr[] and D\<^sub>G[] and [] and [] and Dom'[]
    from Dom'
    obtain y where Dom[useful]: \<open>y \<in> D\<close>
               and x_def[simp]: \<open>x = (g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c) (case y of (x, w) \<Rightarrow> case getter x of (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<Rightarrow> case h (x\<^sub>b, w) of (y, r) \<Rightarrow> (y, r, x\<^sub>d, x\<^sub>c))\<close>
      by (clarsimp simp add: split_beta)

    note D\<^sub>G' = D\<^sub>G[THEN bspec[OF _ Dom]]
    from EC have db: \<open>?\<^sub>+ True d\<epsilon> = ?\<^sub>+ C\<^sub>d d + ?\<^sub>+ True \<epsilon> \<and> (C\<^sub>c \<longrightarrow> d\<epsilon> ##\<^sub>+ c) \<and> (C\<^sub>d \<longrightarrow> d ##\<^sub>+ \<epsilon>)\<close> by blast
    note t1[useful] = MG[THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF db] ;;

    apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apsnd fst x\<close>]
    certified by (insert t1 Dom, clarsimp simp add: image_iff split: prod.split, force) ;;

    apply_rule apply_Semimodule_One\<^sub>I_\<phi>Some[OF S1\<^sub>I]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                  clarsimp simp add: image_iff split: prod.split) ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_RCond_\<phi>Some[OF SZ, where s=\<open>d\<close> and t=\<epsilon> and r=d\<epsilon> and C=C\<^sub>d
                                                                and x=\<open>case x of (y,r,x\<^sub>d,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (I\<^sub>\<epsilon> x\<^sub>b,x\<^sub>d)\<close>]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                  clarsimp simp add: image_iff split: prod.split, auto_sledgehammer) ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_LCond_\<phi>Some[OF SZ, where s=\<open>d\<epsilon>\<close> and t=c and r=a and C=C\<^sub>c
                                                             and x=\<open>case x of (y,r,x\<^sub>d,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z \<epsilon> d) (I\<^sub>\<epsilon> x\<^sub>b,x\<^sub>d))\<close>]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                  clarsimp simp add: image_iff split: prod.split, auto_sledgehammer)

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, unfold Premise_def conj_imp_eq_imp_imp, rule ballI)
    subgoal premises prems for x proof -
        show ?thesis
          by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                              simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                     \<open>\<forall>x. D\<^sub>G x \<longrightarrow> _\<close> [THEN spec[where x=\<open>fst x\<close>]],
              clarsimp split: prod.split, auto_sledgehammer)
      qed .

(* NOT MAINTAINED BUT DO NOT REMOVE, I am still not sure whether we can leave from conditioned
   split at all.
lemma SE_Module_SDistr_a_d\<epsilon>c_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri
        name: F\<^sub>1.module_mapper\<^sub>a\<^sub>_\<^sub>d\<^sub>\<epsilon>\<^sub>c
        pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> a = d + \<epsilon> + c @action \<A>arith_eq)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds' Dx\<^sub>z z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F\<^sub>1 U \<epsilon> D\<^sub>\<epsilon>\<^sub>E E\<^sub>\<epsilon> Any_P\<^sub>E
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F\<^sub>1 U' \<epsilon> D\<^sub>\<epsilon>\<^sub>I I\<^sub>\<epsilon> Any_P\<^sub>I
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds (d + \<epsilon>) \<and> d + \<epsilon> ##\<^sub>+ c \<and> Ds' (d + \<epsilon>) \<and> Ds' c \<and>
                  Ds d \<and> Ds \<epsilon> \<and> Ds' d \<and> Ds' \<epsilon> \<and> d ##\<^sub>+ \<epsilon>
\<Longrightarrow> module_mapper\<^sub>3\<^sub>\<epsilon> c \<epsilon> d uz z E\<^sub>\<epsilon> I\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I Dx Dx\<^sub>z D\<^sub>G f\<^sub>c f f\<^sub>d f' getter @action \<A>_template_reason undefined

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G \<mapsto> T' \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : U \<^emph>[C\<^sub>W] W \<mapsto> U' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x,w). case getter x of (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)) ` D

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>s\<^sub>m (fst x) \<and> D\<^sub>G (fst x))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R  = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G  \<^emph> \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[True] F\<^sub>1 c @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R' = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G' \<^emph> \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[True] F\<^sub>1 c @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c : T \<^emph>[C\<^sub>R] R \<mapsto> T' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x,w). let (x\<^sub>c, x\<^sub>b, x\<^sub>d) = getter x
                              ; (y,r) = h (x\<^sub>b, w)
                             in (y, r, x\<^sub>d, x\<^sub>c))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(y,r,x\<^sub>d,x\<^sub>c). case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (z c (d + \<epsilon>) (x\<^sub>c, z \<epsilon> d (I\<^sub>\<epsilon> x\<^sub>b, x\<^sub>d)), w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
            Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def module_mapper\<^sub>3\<^sub>\<epsilon>_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises [simp] and SS[] and SZ[] and S1\<^sub>E[] and S1\<^sub>I[] and _ and A and Tr[] and _ and [] and []

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where s=\<open>d+\<epsilon>\<close> and t=c]
    certified by (insert useful(1) useful(2)[THEN bspec[OF _ useful(1)]]
                         A[THEN spec[where x=\<open>fst x\<close>]],
                    clarsimp split: prod.split simp: useful(3-) Let_def) ;;
    
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where s=\<open>d\<close> and t=\<epsilon>]
    certified by (insert useful(1) useful(2)[THEN bspec[OF _ useful(1)]]
                         A[THEN spec[where x=\<open>fst x\<close>]],
                    clarsimp split: prod.split simp: useful(3-) Let_def) ;;

    apply_rule apply_Semimodule_One\<^sub>E_\<phi>Some[OF S1\<^sub>E]
    certified by (insert useful(1) useful(2)[THEN bspec[OF _ useful(1)]]
                         A[THEN spec[where x=\<open>fst x\<close>]],
                    clarsimp split: prod.split simp: useful(3-) Let_def) ;;

    apply_rule ToA_Mapper_onward[OF Tr,
        where x=\<open>case x of (x,w) \<Rightarrow> case getter x of (x\<^sub>c, x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)\<close>]
      certified by (insert A[THEN spec[where x=\<open>fst x\<close>]]
                           useful(2) useful(3)[THEN bspec[OF _ useful(2)]],
                    clarsimp split: prod.split simp: image_iff Let_def, metis prod.inject)
  
  \<medium_right_bracket> certified by (insert A[THEN spec[where x=\<open>fst x\<close>]]
                         useful(3)[THEN bspec[OF _ \<open>x \<in> D\<close>]],
                  clarsimp simp add: image_iff Let_def split: prod.split)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises _ and SS[] and SZ[] and S1\<^sub>E[] and S1\<^sub>I[] and _ and A and Tr[] and _ and [] and []

    apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apsnd fst x\<close>]
    certified apply (insert useful(1), clarsimp simp add: image_iff split: prod.split)
    subgoal premises prems for a b
      by (insert useful(2)[THEN bspec[OF _ \<open>_ \<in> D\<close>]]
                 A[THEN spec[where x=\<open>a\<close>]] prems,
          clarsimp simp: Let_def split: prod.split, force) . ;;

    apply_rule apply_Semimodule_One\<^sub>I_\<phi>Some[OF S1\<^sub>I]
    certified apply (insert useful(1), clarsimp simp add: image_iff split: prod.split)
              subgoal premises prems for a b
                by (insert prems useful(2)[THEN bspec[OF _ prems(1)]]
                           ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ prems(1)]]
                           A[THEN spec[where x=\<open>a\<close>]],
                    clarsimp simp: Let_def) . ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ, where s=\<open>d\<close> and t=\<epsilon>
                                                                and x=\<open>case x of (y,r,x\<^sub>d,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (I\<^sub>\<epsilon> x\<^sub>b,x\<^sub>d)\<close>]
    certified apply (insert useful(2), clarsimp simp add: image_iff split: prod.split)
              subgoal premises prems for a b
                by (insert useful(3)[THEN bspec[OF _ prems(1)]]
                           ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ prems(1)]]
                           A[THEN spec[where x=\<open>a\<close>]],
                    insert prems, clarsimp simp: Let_def useful(4-), case_tac \<open>h (E\<^sub>\<epsilon> xaa, b)\<close>, clarsimp) . ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ, where s=\<open>d+\<epsilon>\<close> and t=c
                                                            and x=\<open>case x of (y,r,x\<^sub>d,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (x\<^sub>c, z \<epsilon> d (I\<^sub>\<epsilon> x\<^sub>b,x\<^sub>d))\<close>]
    certified apply (insert useful(2), clarsimp)
              subgoal premises prems for xa aa aaa ba ab bb
                by (insert prems ToA_Mapper_f_expn_rev[OF Tr, simplified, THEN bspec[OF _ \<open>(ab, bb) \<in> D\<close>]]
                           useful(3)[THEN bspec[OF _ \<open>(ab, bb) \<in> D\<close>]]
                           A[THEN spec[where x=\<open>ab\<close>]],
                    clarsimp simp add: image_iff useful(4-) split: prod.split,
                    case_tac \<open>h (E\<^sub>\<epsilon> xaa, bb)\<close>, clarsimp) .

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, unfold Premise_def conj_imp_eq_imp_imp, rule ballI)
    subgoal premises prems for x proof -
      show ?thesis
        by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                            simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                      \<open>\<forall>x. D\<^sub>G x \<longrightarrow> _\<close> [THEN spec[where x=\<open>fst x\<close>]],
            clarsimp split: prod.split, auto_sledgehammer)
    qed .


lemma SE_Module_SDistr_a_\<epsilon>c_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri
        name: F\<^sub>1.module_mapper\<^sub>a\<^sub>_\<^sub>\<epsilon>\<^sub>c
        pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> a = \<epsilon> + c @action \<A>arith_eq)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds' Dx\<^sub>z z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F\<^sub>1 U \<epsilon> D\<^sub>\<epsilon>\<^sub>E E\<^sub>\<epsilon> Any_P\<^sub>E
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F\<^sub>1 U' \<epsilon> D\<^sub>\<epsilon>\<^sub>I I\<^sub>\<epsilon> Any_P\<^sub>I
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds c \<and> Ds \<epsilon> \<and> \<epsilon> ##\<^sub>+ c \<and> Ds' \<epsilon> \<and> Ds' c
\<Longrightarrow> module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R c \<epsilon> uz z E\<^sub>\<epsilon> I\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I Dx Dx\<^sub>z D\<^sub>G f\<^sub>c f f' getter @action \<A>_template_reason None

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G \<mapsto> T' \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : U \<^emph>[C\<^sub>W] W \<mapsto> U' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x,w). case getter x of (x\<^sub>c, x\<^sub>b) \<Rightarrow> (x\<^sub>b, w)) ` D

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>s\<^sub>m (fst x) \<and> D\<^sub>G (fst x))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R  = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G  \<^emph> \<half_blkcirc>[True] F\<^sub>1 c @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R' = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G' \<^emph> \<half_blkcirc>[True] F\<^sub>1 c @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>c : T \<^emph>[C\<^sub>R] R \<mapsto> T' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x,w). let (x\<^sub>c, x\<^sub>b) = getter x
                              ; (y,r) = h (x\<^sub>b, w)
                             in (y, r, x\<^sub>c))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(y,r,x\<^sub>c). case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (z c \<epsilon> (x\<^sub>c, I\<^sub>\<epsilon> x\<^sub>b), w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
            Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>R_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises _ and SS[] and SZ[] and S1\<^sub>E[] and S1\<^sub>I[]and _ and A  and Tr[] and _ and [] and []

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where s=\<open>\<epsilon>\<close> and t=c]
    certified by (insert useful(1) useful(2)[THEN bspec[OF _ useful(1)]]
                         A[THEN spec[where x=\<open>fst x\<close>]],
                    clarsimp split: prod.split simp: useful(3-) Let_def) ;;

    apply_rule apply_Semimodule_One\<^sub>E_\<phi>Some[OF S1\<^sub>E]
    certified by (insert useful(1) useful(2)[THEN bspec[OF _ useful(1)]]
                         A[THEN spec[where x=\<open>fst x\<close>]],
                    clarsimp split: prod.split simp: useful(3-) Let_def) ;;

    apply_rule ToA_Mapper_onward[OF Tr,
        where x=\<open>case x of (x,w) \<Rightarrow> case getter x of (x\<^sub>c, x\<^sub>b) \<Rightarrow> (x\<^sub>b, w)\<close>]
      certified by (insert A[THEN spec[where x=\<open>fst x\<close>]]
                           useful(2) useful(3)[THEN bspec[OF _ useful(2)]]
                           A[THEN spec[where x=\<open>fst x\<close>]],
                    clarsimp split: prod.split simp: image_iff Let_def,
                    metis Pair_inject)
  \<medium_right_bracket> certified by (insert A[THEN spec[where x=\<open>fst x\<close>]]
                         useful(3)[THEN bspec[OF _ \<open>x \<in> D\<close>]],
                  clarsimp simp add: image_iff Let_def split: prod.split)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises _ and SS[] and SZ[] and S1\<^sub>E[] and S1\<^sub>I[] and _ and A and Tr[] and _ and [] and []

    apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apsnd fst x\<close>]
    certified apply (insert useful(1), clarsimp simp add: image_iff split: prod.split)
    subgoal premises prems for a b
      by (insert useful(2)[THEN bspec[OF _ \<open>_ \<in> D\<close>]]
                 A[THEN spec[where x=\<open>a\<close>]]
                 prems,
          clarsimp simp: Let_def split: prod.split, force) . ;;

    apply_rule apply_Semimodule_One\<^sub>I_\<phi>Some[OF S1\<^sub>I]
    certified apply (insert useful(1), clarsimp simp add: image_iff split: prod.split)
              subgoal premises prems for a b
                by (insert prems useful(2)[THEN bspec[OF _ prems(1)]]
                           ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ prems(1)]]
                           A[THEN spec[where x=\<open>a\<close>]],
                    clarsimp simp: Let_def) . ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ, where s=\<open>\<epsilon>\<close> and t=c
                                                            and x=\<open>case x of (y,r,x\<^sub>c) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (x\<^sub>c, I\<^sub>\<epsilon> x\<^sub>b)\<close>]
    certified apply (insert useful(2), clarsimp)
              subgoal premises prems for xa a b aa ba
                by (insert prems ToA_Mapper_f_expn_rev[OF Tr, simplified, THEN bspec[OF _ \<open>(aa, ba) \<in> D\<close>]]
                           useful(3)[THEN bspec[OF _ \<open>(aa, ba) \<in> D\<close>]]
                           A[THEN spec[where x=\<open>aa\<close>]],
                    clarsimp simp add: image_iff useful(4-) split: prod.split,
                    case_tac \<open>h (E\<^sub>\<epsilon> y, ba)\<close>, clarsimp) .

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, unfold Premise_def conj_imp_eq_imp_imp, rule ballI)
    subgoal premises prems for x proof -
      show ?thesis
        by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                            simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                   \<open>\<forall>x. D\<^sub>G x \<longrightarrow> _\<close> [THEN spec[where x=\<open>fst x\<close>]],
            clarsimp split: prod.split, auto_sledgehammer)
    qed .
*)


lemma SE_Module_SDistr_a_d\<epsilon>_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri name: F\<^sub>1.module_mapper\<^sub>a\<^sub>_\<^sub>d\<^sub>\<epsilon>]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 d \<epsilon> a)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds Dx uz
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1' Ds' Dx\<^sub>z z
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F\<^sub>1 U \<epsilon> D\<^sub>\<epsilon>\<^sub>E E\<^sub>\<epsilon> Any_P\<^sub>E
\<Longrightarrow> TERM Semimodule_One\<^sub>I F\<^sub>3 T \<epsilon> D\<^sub>\<epsilon>\<^sub>I\<^sub>T I\<^sub>\<epsilon>\<^sub>T Any_P\<^sub>I\<^sub>T
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F\<^sub>1' U' \<epsilon> D\<^sub>\<epsilon>\<^sub>I I\<^sub>\<epsilon> Any_P\<^sub>I
\<Longrightarrow> TERM Semimodule_One\<^sub>E F\<^sub>3' T' \<epsilon> D\<^sub>\<epsilon>\<^sub>E\<^sub>T E\<^sub>\<epsilon>\<^sub>T Any_P\<^sub>E\<^sub>T

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds \<epsilon> \<and> Ds' d \<and> Ds' \<epsilon>
\<Longrightarrow> module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L \<epsilon> d uz z E\<^sub>\<epsilon> I\<^sub>\<epsilon> D\<^sub>\<epsilon>\<^sub>E D\<^sub>\<epsilon>\<^sub>I Dx Dx\<^sub>z D\<^sub>G f f\<^sub>d f' getter

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G \<mapsto> T' \<^emph>[C\<^sub>R\<^sub>G] R\<^sub>G'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : U \<^emph>[C\<^sub>W] W \<mapsto> U' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x,w). case getter x of (x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)) ` D

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. D\<^sub>G (fst x))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R  = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G  \<^emph> \<half_blkcirc>[True] F\<^sub>1 d @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>R] R' = \<half_blkcirc>[C\<^sub>R\<^sub>G] R\<^sub>G' \<^emph> \<half_blkcirc>[True] F\<^sub>1' d @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d : T \<^emph>[C\<^sub>R] R \<mapsto> T' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1' a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x,w). let (x\<^sub>b, x\<^sub>d) = getter x
                              ; (y,r) = h (x\<^sub>b, w)
                             in (y, r, x\<^sub>d))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(y,r,x\<^sub>d). case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (z \<epsilon> d (I\<^sub>\<epsilon> x\<^sub>b,x\<^sub>d), w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
            Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def module_mapper\<^sub>2\<^sub>\<epsilon>\<^sub>L_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises EC[unfolded equation\<^sub>2\<^sub>1_def] and SS[] and SZ[] and S1\<^sub>E[] and [] and S1\<^sub>I[] and [] and _
         and MG and Tr[] and D\<^sub>G[] and [] and [] and Dom[useful]
    note D\<^sub>G' = D\<^sub>G[THEN bspec[OF _ Dom]]
    note t1[useful] = MG[THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]]
    note EC[THEN conjunct2, simp] ;;
    
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where s=\<open>d\<close> and t=\<epsilon>, unfolded EC[THEN conjunct1]]

    apply_rule apply_Semimodule_One\<^sub>E_\<phi>Some[OF S1\<^sub>E]

    apply_rule ToA_Mapper_onward[OF Tr,
        where x=\<open>case x of (x,w) \<Rightarrow> case getter x of (x\<^sub>b, x\<^sub>d) \<Rightarrow> (x\<^sub>b, w)\<close>]
      certified by (insert t1, clarsimp split: prod.split simp: image_iff Let_def, auto_sledgehammer)

  \<medium_right_bracket> certified by (insert t1, clarsimp simp add: image_iff Let_def split: prod.split)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises EC[unfolded equation\<^sub>2\<^sub>1_def, simp] and SS[] and SZ[] and S1\<^sub>E[] and [] and S1\<^sub>I[] and [] and _
         and MG and Tr[] and D\<^sub>G[] and [] and [] and Dom'[]

    from Dom'
    obtain y where Dom[useful]: \<open>y \<in> D\<close>
               and x_def[simp]: \<open>x = (g \<otimes>\<^sub>f r \<otimes>\<^sub>f f\<^sub>d) (case y of (x, w) \<Rightarrow> case getter x of (x\<^sub>b, x\<^sub>d) \<Rightarrow> case h (x\<^sub>b, w) of (y, r) \<Rightarrow> (y, r, x\<^sub>d))\<close>
      by (clarsimp simp add: split_beta)

    note D\<^sub>G' = D\<^sub>G[THEN bspec[OF _ Dom]]
    note t1[useful] = MG[THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]] ;;

    apply_rule ToA_Mapper_backward[OF Tr, where x=\<open>apsnd fst x\<close>]
    certified by (insert t1 Dom, clarsimp simp add: image_iff split: prod.split, force) ;;

    apply_rule apply_Semimodule_One\<^sub>I_\<phi>Some[OF S1\<^sub>I]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                  clarsimp simp add: image_iff split: prod.split);;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ, where s=\<open>d\<close> and t=\<epsilon>
                                                            and x=\<open>case x of (y,r,x\<^sub>d) \<Rightarrow> case s (y,r) of (x\<^sub>b,w) \<Rightarrow> (I\<^sub>\<epsilon> x\<^sub>b,x\<^sub>d)\<close>]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                  clarsimp simp add: image_iff split: prod.split, auto_sledgehammer) ;;

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, unfold Premise_def conj_imp_eq_imp_imp, rule ballI)
    subgoal premises prems for x proof -
      show ?thesis
        by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                            simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                   \<open>\<forall>x. D\<^sub>G x \<longrightarrow> _\<close> [THEN spec[where x=\<open>fst x\<close>]],
            clarsimp split: prod.split, auto_sledgehammer)
    qed .




lemma SE_Module_SDistr_dac_b_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri name: F\<^sub>1.module_mapper\<^sub>d\<^sub>a\<^sub>c\<^sub>_\<^sub>b]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d a da c b)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds' Dx\<^sub>S uz
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (C\<^sub>d \<longrightarrow> Ds d \<and> Ds a \<and> Ds' d \<and> Ds' a) \<and>
                  (C\<^sub>c \<longrightarrow> Ds da \<and> Ds c \<and> Ds' da \<and> Ds' c)
\<Longrightarrow> module_mapper\<^sub>1\<^sub>3\<^sub>C C\<^sub>c C\<^sub>d d a da c uz z Dx\<^sub>S Dx D\<^sub>G f\<^sub>d f\<^sub>a f\<^sub>c f getter

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 b \<^emph>[C\<^sub>W\<^sub>G] W\<^sub>G \<mapsto> F\<^sub>1 b \<^emph>[C\<^sub>W\<^sub>G] W\<^sub>G'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c,w). (getter (x\<^sub>a,x\<^sub>d,x\<^sub>c), w)) ` D

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>(x\<^sub>a,x\<^sub>d,x\<^sub>c,w)\<in>D. D\<^sub>G (x\<^sub>a,x\<^sub>d,x\<^sub>c))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W  = \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>G] W\<^sub>G  @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W' = \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>G] W\<^sub>G' @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f\<^sub>a \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c,w). h (getter (x\<^sub>a,x\<^sub>d,x\<^sub>c), w))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>yr. let (x\<^sub>b,w) = s yr
                           ; (x\<^sub>c,x\<^sub>d\<^sub>a) = ?\<^sub>s\<^sub>L C\<^sub>c (uz c da) x\<^sub>b
                           ; (x\<^sub>a,x\<^sub>d) = ?\<^sub>s\<^sub>R C\<^sub>d (uz a d) x\<^sub>d\<^sub>a
                          in (x\<^sub>a,x\<^sub>d,x\<^sub>c,w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>
  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises EC[unfolded equation\<^sub>3\<^sub>1_cond_def, simp] and SZ[] and [] and [simp]
         and MG and Tr[] and D\<^sub>G[] and [] and [] and Dom
    from D\<^sub>G[THEN bspec[OF _ Dom]]
    have D\<^sub>G': \<open>D\<^sub>G (case x of (x\<^sub>a, x\<^sub>d, x\<^sub>c, w) \<Rightarrow> (x\<^sub>a, x\<^sub>d, x\<^sub>c))\<close> by (cases x; clarsimp)
    note t1[useful] = MG[unfolded module_mapper\<^sub>1\<^sub>3\<^sub>C_def, THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]] ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_RCond_\<phi>Some[OF SZ, where s=d and t=a and r=da and C=C\<^sub>d
                                                                  and x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (x\<^sub>a, x\<^sub>d)\<close>]
    certified by (insert t1 Dom, clarsimp split: prod.split) ;;
      
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_LCond_\<phi>Some[OF SZ, where s=da and t=c and r=b and C=C\<^sub>c
                                                                  and x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (x\<^sub>a, x\<^sub>d))\<close>]
    certified by (insert t1 Dom, clarsimp split: prod.split) ;;

    apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (?\<^sub>j\<^sub>L C\<^sub>c (z c da) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (x\<^sub>a, x\<^sub>d)), w)\<close>]
    certified by (insert t1 Dom, clarsimp split: prod.split simp: image_iff, auto_sledgehammer)
  \<medium_right_bracket> certified by (insert t1 Dom, clarsimp split: prod.split simp: image_iff)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises EC[unfolded equation\<^sub>3\<^sub>1_cond_def, simp] and SZ[] and SS[] and [simp]
         and MG and Tr[] and D\<^sub>G[] and [] and [] and Dom'[]

    from Dom'
    obtain y where Dom[useful]: \<open>y \<in> D\<close>
               and x_def[simp]: \<open>x = (g \<otimes>\<^sub>f r) (case y of (x\<^sub>a, x\<^sub>d, x\<^sub>c, w) \<Rightarrow> h (getter (x\<^sub>a, x\<^sub>d, x\<^sub>c), w))\<close>
      by (clarsimp, metis map_prod_simp)

    from D\<^sub>G[THEN bspec[OF _ Dom]]
    have D\<^sub>G': \<open>D\<^sub>G (case y of (x\<^sub>a, x\<^sub>d, x\<^sub>c, w) \<Rightarrow> (x\<^sub>a, x\<^sub>d, x\<^sub>c))\<close> by (cases x; clarsimp)
    note t1[useful] = MG[unfolded module_mapper\<^sub>1\<^sub>3\<^sub>C_def, THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]] ;;

    apply_rule ToA_Mapper_backward[OF Tr, where x=x]
    certified by (insert t1 Dom, clarsimp split: prod.split simp: image_iff, force) ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_LCond_\<phi>Some[OF SS, where x=\<open>(fst o s) x\<close> and s=da and t=c and r=b and C=C\<^sub>c]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                 clarsimp split: prod.split simp: image_iff) ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_RCond_\<phi>Some[OF SS, where s=d and t=a and r=da and C=C\<^sub>d and x=\<open>(snd o ?\<^sub>s\<^sub>L C\<^sub>c (uz c da) o fst o s) x\<close>]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                 clarsimp split: prod.split simp: image_iff)

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, rule, unfold Premise_def conj_imp_eq_imp_imp module_mapper\<^sub>1\<^sub>3\<^sub>C_def)
  subgoal premises prems for x proof -
    from \<open>\<forall>(x\<^sub>a, x\<^sub>d, x\<^sub>c, w)\<in>D. D\<^sub>G (x\<^sub>a, x\<^sub>d, x\<^sub>c)\<close>[THEN bspec[OF _ \<open>x \<in> D\<close>]]
    have D\<^sub>G': \<open>D\<^sub>G (case x of (x\<^sub>a, x\<^sub>d, x\<^sub>c, w) \<Rightarrow> (x\<^sub>a, x\<^sub>d, x\<^sub>c))\<close> by (cases x; clarsimp)

    show ?thesis
      by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                          simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                 \<open>\<forall>x. D\<^sub>G x \<longrightarrow> _\<close>[THEN spec, THEN mp, OF D\<^sub>G'],
          cases x, clarsimp split: prod.split,
          case_tac \<open>?\<^sub>s\<^sub>L C\<^sub>c (uz c da) (f (?\<^sub>j\<^sub>L C\<^sub>c (z c da) (ca, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (aa, b))))\<close>, clarsimp,
          case_tac \<open>?\<^sub>s\<^sub>R C\<^sub>d (uz a d) ba\<close>, clarsimp,
          metis Pair_inject equation\<^sub>3\<^sub>1_cond_def prems(1))
  qed .


(*depreciated, I believe, we only need to provide the identity element version for a_d\<epsilon>c situation

lemma SE_Module_SDistr_d\<epsilon>c_b_ToA_mapper_cond
      [\<phi>reason_template name: F\<^sub>1.module_mapper\<^sub>d\<^sub>\<epsilon>\<^sub>c\<^sub>_\<^sub>b_cond[]]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>3\<^sub>1_cond C\<^sub>d C\<^sub>c d \<epsilon> d\<epsilon> c b)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds' Dx\<^sub>S uz
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>E F\<^sub>1 U \<epsilon> D\<^sub>\<epsilon>\<^sub>E E\<^sub>\<epsilon> Any_P\<^sub>E
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_One\<^sub>I F\<^sub>1 U' \<epsilon> D\<^sub>\<epsilon>\<^sub>I I\<^sub>\<epsilon> Any_P\<^sub>I
\<Longrightarrow> NO_MATCH (\<epsilon>'::'s'::partial_ab_semigroup_add) \<epsilon> @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (C\<^sub>d \<longrightarrow> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds' d \<and> Ds' a) \<and>
                  (C\<^sub>c \<longrightarrow> Ds da \<and> Ds c \<and> da ##\<^sub>+ c \<and> Ds' da \<and> Ds' c)

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : T \<^emph>[C\<^sub>R] R \<mapsto> T' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : U \<^emph>[C\<^sub>W\<^sub>G] W\<^sub>G \<mapsto> U' \<^emph>[C\<^sub>W\<^sub>G] W\<^sub>G'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c,w). (?\<^sub>j\<^sub>L C\<^sub>c (z c da) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (x\<^sub>a, x\<^sub>d)), w)) ` D

\<Longrightarrow> separatable_module_zip\<^sub>3\<^sub>1 (?\<^sub>s\<^sub>R C\<^sub>d (uz a d)) (?\<^sub>s\<^sub>L C\<^sub>c (uz c da))
                            (?\<^sub>j\<^sub>L C\<^sub>c (z c da)) (?\<^sub>j\<^sub>R C\<^sub>d (z a d))
                             D\<^sub>s\<^sub>m f f\<^sub>c f' f\<^sub>d
    \<comment> \<open>the antecedent is solved at runtime but not instantiation-time because we rely on runtime
        assignment of \<open>C\<^sub>d\<close> and \<open>C\<^sub>c\<close> to eliminate \<open>?\<^sub>s\<^sub>R C\<^sub>d\<close> etc.\<close>

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. let (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) = x
                    ; y = f (?\<^sub>j\<^sub>L C\<^sub>c (z c da) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (x\<^sub>a, x\<^sub>d)))
                    ; (y\<^sub>c,y\<^sub>d\<^sub>a) = ?\<^sub>s\<^sub>L C\<^sub>c (uz c da) y
                   in (C\<^sub>d \<longrightarrow> Dx a d (x\<^sub>a, x\<^sub>d) \<and>
                              Dx\<^sub>S a d y\<^sub>d\<^sub>a) \<and>
                      (C\<^sub>c \<longrightarrow> Dx c da (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (x\<^sub>a, x\<^sub>d)) \<and>
                              Dx\<^sub>S c da y) \<and>
                      D\<^sub>s\<^sub>m (x\<^sub>c,x\<^sub>a,x\<^sub>d))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W  = \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>G] W\<^sub>G  @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W' = \<half_blkcirc>[C\<^sub>d] F\<^sub>1 d \<^emph> \<half_blkcirc>[C\<^sub>c] F\<^sub>1 c \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>G] W\<^sub>G' @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c,w). h (?\<^sub>j\<^sub>L C\<^sub>c (z c da) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (x\<^sub>a, x\<^sub>d)), w))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>yr. let (x\<^sub>b,w) = s yr
                           ; (x\<^sub>c,x\<^sub>d\<^sub>a) = ?\<^sub>s\<^sub>L C\<^sub>c (uz c da) x\<^sub>b
                           ; (x\<^sub>a,x\<^sub>d) = ?\<^sub>s\<^sub>R C\<^sub>d (uz a d) x\<^sub>d\<^sub>a
                          in (x\<^sub>a,x\<^sub>d,x\<^sub>c,w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>
 unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises [symmetric, simp] and SZ[] and [] and [simp] and _ and Tr[] and []
         and _ and [] and [] and _
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_RCond_\<phi>Some[OF SZ, where s=d and t=a and r=da and C=C\<^sub>d
                                                                  and x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (x\<^sub>a, x\<^sub>d)\<close>]
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_LCond_\<phi>Some[OF SZ, where s=da and t=c and r=b and C=C\<^sub>c
                                                                  and x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (x\<^sub>a, x\<^sub>d))\<close>]
    apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (?\<^sub>j\<^sub>L C\<^sub>c (z c da) (x\<^sub>c, ?\<^sub>j\<^sub>R C\<^sub>d (z a d) (x\<^sub>a, x\<^sub>d)), w)\<close>]
  \<medium_right_bracket> apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises [symmetric, simp] and SZ[] and SS[] and [simp] and _ and Tr[] and []
         and _ and [] and [] and _
    apply_rule ToA_Mapper_backward[OF Tr, where x=x]
      certified by (insert useful(1), simp add: image_image image_iff, elim bexE, simp add: prod.case_distrib, force) ;;
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_LCond_\<phi>Some[OF SS, where x=\<open>(fst o s) x\<close> and s=da and t=c and r=b and C=C\<^sub>c]
    certified apply (insert useful(1), simp add: image_image image_iff, elim bexE)
              subgoal premises prems for y
                by (insert useful(2)[THEN bspec[OF _ prems(1)]]
                                     ToA_Mapper_f_expn_rev[OF Tr, simplified, THEN bspec[OF _ prems(1)]]
                                     prems(2),
                    clarsimp split: prod.split simp add: useful(3-)) . ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_RCond_\<phi>Some[OF SS, where s=d and t=a and r=da and C=C\<^sub>d and x=\<open>(snd o ?\<^sub>s\<^sub>L C\<^sub>c (uz c da) o fst o s) x\<close>]
    certified apply (insert useful(1), simp add: image_image image_iff, elim bexE)
              subgoal premises prems for y
                by (insert useful(2)[THEN bspec[OF _ prems(1)]]
                           ToA_Mapper_f_expn_rev[OF Tr, simplified, THEN bspec[OF _ prems(1)]]
                           prems(2),
                    clarsimp simp add: useful(4-)) .
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, rule, unfold Premise_def conj_imp_eq_imp_imp)
    subgoal premises prems for x proof -
        have t2: \<open>D\<^sub>s\<^sub>m (case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (x\<^sub>c,x\<^sub>a,x\<^sub>d))\<close>
          by (insert \<open>\<forall>_ \<in> D. _\<close>[THEN bspec[OF _ \<open>x \<in> D\<close>]], clarsimp)

        show ?thesis
          by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                              simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                     \<open>separatable_module_zip\<^sub>3\<^sub>1 _ _ _ _ _ _ _ _ _\<close>
                                          [unfolded separatable_module_zip\<^sub>3\<^sub>1_def, THEN spec, THEN mp, OF t2],
              cases x, clarsimp split: prod.split)
      qed .
*)


(* depreciated, use conditioned version instead

lemma SE_Module_SDistr_dac_b_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri
        name: F\<^sub>1.module_mapper\<^sub>d\<^sub>a\<^sub>c\<^sub>_\<^sub>b
        pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> d + a + c = b @action \<A>arith_eq)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds' Dx\<^sub>S uz
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds' d \<and> Ds' a \<and>
                  Ds (d+a) \<and> Ds c \<and> d+a ##\<^sub>+ c \<and> Ds' (d+a) \<and> Ds' c

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 b \<^emph>[C\<^sub>W\<^sub>G] W\<^sub>G \<mapsto> F\<^sub>1 b \<^emph>[C\<^sub>W\<^sub>G] W\<^sub>G'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c,w). (z c (d+a) (x\<^sub>c, z a d (x\<^sub>a, x\<^sub>d)), w)) ` D

\<Longrightarrow> separatable_module_zip\<^sub>3\<^sub>1 (uz a d) (uz c (d+a)) (z c (d+a)) (z a d)
                             D\<^sub>s\<^sub>m f f\<^sub>c f' f\<^sub>d
    @action \<A>_template_reason undefined

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. let (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) = x
                    ; y = f (z c (d+a) (x\<^sub>c, z a d (x\<^sub>a, x\<^sub>d)))
                    ; (y\<^sub>c,y\<^sub>d\<^sub>a) = uz c (d+a) y
                   in Dx a d (x\<^sub>a, x\<^sub>d) \<and> Dx\<^sub>S a d y\<^sub>d\<^sub>a \<and>
                      Dx c (d+a) (x\<^sub>c, z a d (x\<^sub>a, x\<^sub>d)) \<and> Dx\<^sub>S c (d+a) y \<and>
                      D\<^sub>s\<^sub>m (x\<^sub>c,x\<^sub>a,x\<^sub>d))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W  = \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[True] F\<^sub>1 c \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>G] W\<^sub>G  @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W' = \<half_blkcirc>[True] F\<^sub>1 d \<^emph> \<half_blkcirc>[True] F\<^sub>1 c \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>G] W\<^sub>G' @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f f\<^sub>c \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x\<^sub>a,x\<^sub>d,x\<^sub>c,w). h (z c (d+a) (x\<^sub>c, z a d (x\<^sub>a, x\<^sub>d)), w))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>yr. let (x\<^sub>b,w) = s yr
                           ; (x\<^sub>c,x\<^sub>d\<^sub>a) = uz c (d+a) x\<^sub>b
                           ; (x\<^sub>a,x\<^sub>d) = uz a d x\<^sub>d\<^sub>a
                          in (x\<^sub>a,x\<^sub>d,x\<^sub>c,w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises [simp] and SZ[] and [] and _ and Tr[] and []
         and _ and [] and [] and _

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ, where s=d and t=a
                                                            and x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (x\<^sub>a, x\<^sub>d)\<close>]
    certified by (insert useful(2)[THEN bspec[OF _ useful(1)]], clarsimp simp: useful(1,3-) Let_def split: prod.split) ;;
    
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ, where s=\<open>d+a\<close> and t=c
                                                            and x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (x\<^sub>c, z a d (x\<^sub>a, x\<^sub>d))\<close>]
    certified by (insert useful(2)[THEN bspec[OF _ useful(1)]], clarsimp simp: useful(1,3-) Let_def split: prod.split) ;;

    apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (z c (d+a) (x\<^sub>c, z a d (x\<^sub>a, x\<^sub>d)), w)\<close>]
    certified by (insert useful(2)[THEN bspec[OF _ useful(1)]], clarsimp simp: useful(1,3-) Let_def split: prod.split)
  \<medium_right_bracket> apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises A and SZ[] and SS[] and _ and Tr[] and []
         and _ and [] and [] and _
    apply_rule ToA_Mapper_backward[OF Tr, where x=x]
    certified by (insert useful(1), clarsimp split: prod.split simp: image_iff, force) ;;
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where x=\<open>(fst o s) x\<close> and s=\<open>d+a\<close> and t=c, unfolded A]
    certified apply (insert useful(1), simp add: image_image image_iff, elim bexE)
              subgoal premises prems for y
                by (insert useful(2)[THEN bspec[OF _ prems(1)]]
                                     ToA_Mapper_f_expn_rev[OF Tr, simplified, THEN bspec[OF _ prems(1)]]
                                     prems(2),
                    clarsimp split: prod.split simp add: useful(3-) Let_def) . ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where s=d and t=a and x=\<open>(snd o uz c (d+a) o fst o s) x\<close>]
    certified apply (insert useful(1), simp add: image_image image_iff, elim bexE)
              subgoal premises prems for y
                by (insert useful(2)[THEN bspec[OF _ prems(1)]]
                           ToA_Mapper_f_expn_rev[OF Tr, simplified, THEN bspec[OF _ prems(1)]]
                           prems(2),
                    clarsimp simp add: useful(4-) Let_def) .
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, rule, unfold Premise_def conj_imp_eq_imp_imp)
    subgoal premises prems for x proof -
        have t2: \<open>D\<^sub>s\<^sub>m (case x of (x\<^sub>a,x\<^sub>d,x\<^sub>c,w) \<Rightarrow> (x\<^sub>c,x\<^sub>a,x\<^sub>d))\<close>
          by (insert \<open>\<forall>_ \<in> D. _\<close>[THEN bspec[OF _ \<open>x \<in> D\<close>]], clarsimp simp add: Let_def)

        show ?thesis
          by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                              simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                     \<open>separatable_module_zip\<^sub>3\<^sub>1 _ _ _ _ _ _ _ _ _\<close>
                                          [unfolded separatable_module_zip\<^sub>3\<^sub>1_def, THEN spec, THEN mp, OF t2],
              cases x, clarsimp split: prod.split)
      qed .


lemma SE_Module_SDistr_ac_b_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri
        name: F\<^sub>1.module_mapper\<^sub>a\<^sub>c\<^sub>_\<^sub>b
        pass: phi_TA_semimodule_sdistrib_rule_pass_no_comm_scalar]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> a + c = b @action \<A>arith_eq)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds' Dx\<^sub>S uz
\<Longrightarrow> NO_MATCH (a'::'s'::partial_ab_semigroup_add) a @action \<A>_template_reason None
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds a \<and> Ds c \<and> a ##\<^sub>+ c \<and> Ds' a \<and> Ds' c

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 b \<^emph>[C\<^sub>W\<^sub>G] W\<^sub>G \<mapsto> F\<^sub>1 b \<^emph>[C\<^sub>W\<^sub>G] W\<^sub>G'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x\<^sub>a,x\<^sub>c,w). (z c a (x\<^sub>c, x\<^sub>a), w)) ` D

\<Longrightarrow> separatable_module_zip\<^sub>2\<^sub>1 (uz c a) (z c a)
                             D\<^sub>s\<^sub>m f f\<^sub>c f' @action \<A>_template_reason undefined

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x\<in>D. let (x\<^sub>a,x\<^sub>c,w) = x
                    ; y = f (z c a (x\<^sub>c,x\<^sub>a))
                    ; (y\<^sub>c,y\<^sub>a) = uz c a y
                   in Dx c a (x\<^sub>c, x\<^sub>a) \<and>
                      Dx\<^sub>S c a y \<and>
                      D\<^sub>s\<^sub>m (x\<^sub>c,x\<^sub>a))

\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W  = \<half_blkcirc>[True] F\<^sub>1 c \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>G] W\<^sub>G  @action \<A>merge
\<Longrightarrow> \<half_blkcirc>[C\<^sub>W] W' = \<half_blkcirc>[True] F\<^sub>1 c \<^emph> \<half_blkcirc>[C\<^sub>W\<^sub>G] W\<^sub>G' @action \<A>merge

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f' \<otimes>\<^sub>f f\<^sub>c \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 a \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x\<^sub>a,x\<^sub>c,w). h (z c a (x\<^sub>c, x\<^sub>a), w))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>yr. let (x\<^sub>b,w) = s yr
                           ; (x\<^sub>c,x\<^sub>a) = uz c a x\<^sub>b
                          in (x\<^sub>a,x\<^sub>c,w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_add_magma \<Rightarrow> ('c::sep_ab_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises [simp] and SZ[] and [] and [simp] and Tr[] and [] and _ and [] and []
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ, where s=a and t=c
                                                            and x=\<open>case x of (x\<^sub>a,x\<^sub>c,w) \<Rightarrow> (x\<^sub>c,x\<^sub>a)\<close>] ;;

    apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>case x of (x\<^sub>a,x\<^sub>c,w) \<Rightarrow> (z c a (x\<^sub>c, x\<^sub>a), w)\<close>]
  \<medium_right_bracket> apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises A[] and SZ[] and SS[] and [simp] and Tr[] and [] and _ and [] and []
    apply_rule ToA_Mapper_backward[OF Tr, where x=x]
      certified by (insert useful(1), simp add: image_image image_iff, elim bexE, simp add: prod.case_distrib, force) ;;
    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where x=\<open>(fst o s) x\<close> and s=a and t=c, unfolded A]
    certified apply (insert useful(1), simp add: image_image image_iff, elim bexE)
              subgoal premises prems for y
                by (insert useful(2)[THEN bspec[OF _ prems(1)]]
                                     ToA_Mapper_f_expn_rev[OF Tr, simplified, THEN bspec[OF _ prems(1)]]
                                     prems(2),
                    clarsimp split: prod.split) .

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, rule, unfold Premise_def conj_imp_eq_imp_imp)
    subgoal premises prems for x proof -
        have t2: \<open>D\<^sub>s\<^sub>m (case x of (x\<^sub>a,x\<^sub>c,w) \<Rightarrow> (x\<^sub>c,x\<^sub>a))\<close>
          by (insert \<open>\<forall>_ \<in> D. _\<close>[THEN bspec[OF _ \<open>x \<in> D\<close>]], clarsimp)

        show ?thesis
          by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                              simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                     \<open>separatable_module_zip\<^sub>2\<^sub>1 _ _ _ _ _ _\<close>
                                          [unfolded separatable_module_zip\<^sub>2\<^sub>1_def, THEN spec, THEN mp, OF t2],
              cases x, clarsimp split: prod.split)
      qed .
*)

lemma SE_Module_SDistr_da_b_ToA_mapper
      [\<phi>reason_template default %\<phi>mapToA_derived_module_SDistri name F\<^sub>1.module_mapper\<^sub>d\<^sub>a\<^sub>_\<^sub>b]:
  \<open> NO_SIMP (\<g>\<u>\<a>\<r>\<d> equation\<^sub>2\<^sub>1 d a b)
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>Z F\<^sub>1 Ds Dx z
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>3
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul\<^sub>0 F\<^sub>1 F\<^sub>1'
\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> Semimodule_SDistr_Homo\<^sub>S F\<^sub>1 Ds' Dx\<^sub>S uz

\<Longrightarrow> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds d \<and> Ds a \<and> d ##\<^sub>+ a \<and> Ds' d \<and> Ds' a
\<Longrightarrow> module_mapper\<^sub>1\<^sub>2\<^sub>L d a uz z Dx\<^sub>S Dx D\<^sub>G f\<^sub>d f\<^sub>a f

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : F\<^sub>1 b \<^emph>[C\<^sub>W] W \<mapsto> F\<^sub>1 b \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s
      \<i>\<n> (\<lambda>(x\<^sub>a,x\<^sub>d,w). (z a d (x\<^sub>a, x\<^sub>d), w)) ` D

\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>(x\<^sub>a,x\<^sub>d,w)\<in>D. D\<^sub>G (x\<^sub>a, x\<^sub>d))

\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : F\<^sub>3 b \<^emph>[C\<^sub>R] R \<mapsto> F\<^sub>3' b \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f\<^sub>a \<otimes>\<^sub>f f\<^sub>d \<otimes>\<^sub>f w : F\<^sub>1 a \<^emph>[True] (F\<^sub>1 d \<^emph>[C\<^sub>W] W) \<mapsto> F\<^sub>1 a \<^emph>[True] (F\<^sub>1 d \<^emph>[C\<^sub>W] W')
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>(x\<^sub>a,x\<^sub>d,w). h (z a d (x\<^sub>a, x\<^sub>d), w))
         \<s>\<e>\<t>\<t>\<e>\<r> SIMP (\<lambda>yr. let (x\<^sub>b,w) = s yr
                           ; (x\<^sub>a,x\<^sub>d) = uz a d x\<^sub>b
                          in (x\<^sub>a,x\<^sub>d,w))
      \<i>\<n> D \<close>
  for F\<^sub>1 :: \<open>'s::partial_semigroup_add \<Rightarrow> ('c::sep_semigroup, 'a) \<phi>\<close>

  unfolding Action_Tag_def \<r>Guard_def NO_SIMP_def
            Type_Variant_of_the_Same_Scalar_Mul\<^sub>0_def
  apply (simp add: ToA_Mapper_\<phi>Some_rewr_origin;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)

  \<medium_left_bracket> premises EC[unfolded equation\<^sub>2\<^sub>1_def, simp] and SZ[] and [] and [simp]
         and MG and Tr[] and D\<^sub>G[] and Dom

    from D\<^sub>G[THEN bspec[OF _ Dom]]
    have D\<^sub>G': \<open>D\<^sub>G (case x of (x\<^sub>a, x\<^sub>d, w) \<Rightarrow> (x\<^sub>a, x\<^sub>d))\<close> by (cases x; clarsimp)
    note t1[useful] = MG[unfolded module_mapper\<^sub>1\<^sub>2\<^sub>L_def, THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]] ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>Z_\<phi>Some[OF SZ, where s=d and t=a
                                                            and x=\<open>case x of (x\<^sub>a,x\<^sub>d,w) \<Rightarrow> (x\<^sub>a, x\<^sub>d)\<close>]
    certified by (insert t1, clarsimp split: prod.split simp: Let_def)  ;;

    apply_rule ToA_Mapper_onward[OF Tr, where x=\<open>case x of (x\<^sub>a,x\<^sub>d,w) \<Rightarrow> (z a d (x\<^sub>a, x\<^sub>d), w)\<close>]
    certified by (insert \<open>x \<in> D\<close>, clarsimp split: prod.split simp: image_iff, force)
  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule)
  \<medium_left_bracket> premises EC[unfolded equation\<^sub>2\<^sub>1_def, simp] and SZ[] and SS[] and [simp]
         and MG and Tr[] and D\<^sub>G[] and Dom'

    from Dom'
    obtain y where Dom[useful]: \<open>y \<in> D\<close>
               and x_def[simp]: \<open>x = (g \<otimes>\<^sub>f r) (case y of (x\<^sub>a, x\<^sub>d, w) \<Rightarrow> h (z a d (x\<^sub>a, x\<^sub>d), w))\<close>
      by (clarsimp, metis map_prod_simp)

    from D\<^sub>G[THEN bspec[OF _ Dom]]
    have D\<^sub>G': \<open>D\<^sub>G (case y of (x\<^sub>a, x\<^sub>d, w) \<Rightarrow> (x\<^sub>a, x\<^sub>d))\<close> by (cases x; clarsimp)
    note t1[useful] = MG[unfolded module_mapper\<^sub>1\<^sub>2\<^sub>L_def, THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF EC[THEN conjunct2]] ;;

    apply_rule ToA_Mapper_backward[OF Tr, where x=x]
    certified by (insert t1 Dom, clarsimp split: prod.split simp: Let_def image_iff, force) ;;

    apply_rule apply_Semimodule_SDistr_Homo\<^sub>S_\<phi>Some[OF SS, where x=\<open>case s x of (x\<^sub>b,w) \<Rightarrow> x\<^sub>b\<close> and s=d and t=a, unfolded EC[THEN conjunct1]]
    certified by (insert t1 Dom ToA_Mapper_f_expn_rev[OF Tr, simplified Ball_image_comp, THEN bspec[OF _ Dom]],
                  clarsimp split: prod.split simp: Let_def image_iff) ;;

  \<medium_right_bracket> certified by (clarsimp split: prod.split)
    apply (rule conjunctionI, rule, rule, unfold Premise_def conj_imp_eq_imp_imp)
    subgoal premises prems for x proof -

      from \<open>\<forall>(x\<^sub>a, x\<^sub>d, w)\<in>D. D\<^sub>G (x\<^sub>a, x\<^sub>d)\<close>[THEN bspec[OF _ \<open>x \<in> D\<close>]]
      have D\<^sub>G': \<open>D\<^sub>G (case x of (x\<^sub>a, x\<^sub>d, w) \<Rightarrow> (x\<^sub>a, x\<^sub>d))\<close> by (cases x; clarsimp)
      note t1 = \<open>module_mapper\<^sub>1\<^sub>2\<^sub>L d a uz z Dx\<^sub>S Dx D\<^sub>G f\<^sub>d f\<^sub>a f\<close>[unfolded module_mapper\<^sub>1\<^sub>2\<^sub>L_def, THEN spec, THEN mp, OF D\<^sub>G', THEN mp, OF \<open>d ##\<^sub>+ a\<close>]

      show ?thesis
        by (insert ToA_Mapper_f_expn_rev[OF \<open>\<m>\<a>\<p> g \<otimes>\<^sub>f r : _ \<mapsto> _ \<o>\<v>\<e>\<r> f \<otimes>\<^sub>f w : _ \<mapsto> _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> h \<s>\<e>\<t>\<t>\<e>\<r> s \<i>\<n> _\<close>,
                                            simplified, THEN bspec[OF _ \<open>x \<in> D\<close>]]
                   t1,
            cases x, clarsimp split: prod.split)
    qed .


end



subsection \<open>Commutativity between \<phi>-Type Operators\<close>

paragraph \<open>Deriving Rewrites\<close>

(*TODO Tyops_Commute\<^sub>1\<^sub>_\<^sub>2*)

subparagraph \<open>1-to-1\<close>

lemma Comm_Tyops_Rewr_temlpate[\<phi>reason_template name F.G.rewr[]]:
  \<open> Tyops_Commute F F' G G' T D (embedded_func f P)
\<Longrightarrow> Tyops_Commute G' G F' F T D' (embedded_func g Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (g (f x) = x) \<and> D x \<and> D' (f x)
\<Longrightarrow> (x \<Ztypecolon> F (G T)) = (f x \<Ztypecolon> G' (F' T)) \<close>
  unfolding Tyops_Commute_def Premise_def Transformation_def BI_eq_iff
  by clarsimp metis

lemma Comm_Tyops_Rewr\<^sub>2_temlpate[\<phi>reason_template name F.G.rewr[]]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D (embedded_func f P)
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D' (embedded_func g Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> g (f x) = x \<and> D x \<and> D' (f x)
\<Longrightarrow> (x \<Ztypecolon> F (G T U)) = (f x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U)) \<close>
  unfolding BI_eq_iff Premise_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Transformation_def
  by clarsimp metis

subparagraph \<open>1-to-1\<lambda>\<close>

lemma [\<phi>reason_template name F.G.rewr[]]:
  \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>I F F' G G' T D  (embedded_func f P)
\<Longrightarrow> Tyops_Commute\<^sub>\<Lambda>\<^sub>E G' G F' F T D' (embedded_func g Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<and> D' (f x) \<and> g (f x) = x
\<Longrightarrow> (x \<Ztypecolon> F (G T)) = (f x \<Ztypecolon> G' (\<lambda>p. F' (T p))) \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>I_def Tyops_Commute\<^sub>\<Lambda>\<^sub>E_def Transformation_def Premise_def BI_eq_iff
  by clarsimp metis

lemma [\<phi>reason_template name F.G.rewr[]]:
  \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>E F F' G G' T D  (embedded_func f P)
\<Longrightarrow> Tyops_Commute\<^sub>\<Lambda>\<^sub>I G' G F' F T D' (embedded_func g Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<and> D' (f x) \<and> g (f x) = x
\<Longrightarrow> (x \<Ztypecolon> F (\<lambda>p. G (T p))) = (f x \<Ztypecolon> G' (F' T)) \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>I_def Tyops_Commute\<^sub>\<Lambda>\<^sub>E_def Transformation_def Premise_def BI_eq_iff
  by clarsimp metis

subparagraph \<open>1-to-2\<close>

lemma [\<phi>reason_template name F.G.rewr[]]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D  (embedded_func f P)
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D' (embedded_func g Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<and> D' (f x) \<and> g (f x) = x
\<Longrightarrow> (x \<Ztypecolon> F (G T U)) = (f x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U)) \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Transformation_def
            BI_eq_iff
  by clarsimp metis

lemma [\<phi>reason_template name G'.F.rewr[]]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D  (embedded_func f P)
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D' (embedded_func g Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D (g x) \<and> D' x \<and> f (g x) = x
\<Longrightarrow> (x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U)) = (g x \<Ztypecolon> F (G T U)) \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Transformation_def
            BI_eq_iff
  by clarsimp metis


paragraph \<open>Deriving ToA\<close>

subparagraph \<open>1-to-1\<close>

lemma [\<phi>reason_template name F.G.comm[no_atp]]:
  \<open> Tyops_Commute F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (r, RE) = (embedded_func f P, (x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> G' (F' T) \<w>\<i>\<t>\<h> P x)) \<or>\<^sub>c\<^sub>u\<^sub>t
    RE = (x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r x y)
    @action \<A>_template_reason undefined
\<Longrightarrow> RE \<close>
  unfolding Premise_def Action_Tag_def Tyops_Commute_def Orelse_shortcut_def
  by (elim disjE; simp)

subparagraph \<open>1-to-1\<lambda>\<close>

lemma [\<phi>reason_template name F.G.comm[no_atp]]:
  \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>I F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (r, RE) = (embedded_func f P, (x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> G' (\<lambda>p. F' (T p)) \<w>\<i>\<t>\<h> P x)) \<or>\<^sub>c\<^sub>u\<^sub>t
    RE = (x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (\<lambda>p. F' (T p)) \<s>\<u>\<b>\<j> y. r x y) @action \<A>_template_reason undefined
\<Longrightarrow> RE \<close>
  unfolding Premise_def Action_Tag_def Tyops_Commute\<^sub>\<Lambda>\<^sub>I_def Orelse_shortcut_def Transformation_def
  by (elim disjE; simp)

lemma [\<phi>reason_template name F.G.comm[no_atp]]:
  \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>E F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (r, RE) = (embedded_func f P, (x \<Ztypecolon> F (\<lambda>p. G (T p)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> G' (F' T) \<w>\<i>\<t>\<h> P x)) \<or>\<^sub>c\<^sub>u\<^sub>t
    RE = (x \<Ztypecolon> F (\<lambda>p. G (T p)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r x y) @action \<A>_template_reason undefined
\<Longrightarrow> RE \<close>
  unfolding Premise_def Action_Tag_def Tyops_Commute\<^sub>\<Lambda>\<^sub>E_def Orelse_shortcut_def Transformation_def
  by (elim disjE; simp)


subparagraph \<open>1-to-2\<close>

lemma Comm_Tyops\<^sub>1\<^sub>_\<^sub>2_ToA_temlpate[\<phi>reason_template name F.G.comm[no_atp]]:
  \<open> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (r, RE) = (embedded_func f P, (x \<Ztypecolon> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<w>\<i>\<t>\<h> P x)) \<or>\<^sub>c\<^sub>u\<^sub>t
    RE = (x \<Ztypecolon> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r x y) @action \<A>_template_reason undefined
\<Longrightarrow> RE \<close>
  unfolding Premise_def Action_Tag_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Orelse_shortcut_def
  by (elim disjE; simp)

lemma Comm_Tyops\<^sub>2\<^sub>_\<^sub>1_ToA_temlpate[\<phi>reason_template name F.G.comm[no_atp]]:
  \<open> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (r, RE) = (embedded_func f P, (x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F (G T U) \<w>\<i>\<t>\<h> P x)) \<or>\<^sub>c\<^sub>u\<^sub>t
    RE = (x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (G T U) \<s>\<u>\<b>\<j> y. r x y) @action \<A>_template_reason undefined
\<Longrightarrow> RE \<close>
  unfolding Premise_def Action_Tag_def Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Orelse_shortcut_def
  by (elim disjE; simp)


paragraph \<open>Swapping Normalization\<close>

subparagraph \<open>1-to-1\<close>

lemma [\<phi>reason_template name F.G.norm_src [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' y : r x y @action \<A>_template_reason undefined)
\<Longrightarrow> x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r' y @action \<A>_transitive_simp \<close>
  unfolding Transformation_def Action_Tag_def Tyops_Commute_def Premise_def
            Simplify_def Action_Tag_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template name F.G.norm_tgt [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' y : r x y @action \<A>_template_reason undefined)
\<Longrightarrow> x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r' y @action \<A>_backward_transitive_simp \<close>
  unfolding Transformation_def Action_Tag_def Tyops_Commute_def Premise_def
            Simplify_def Action_Tag_def \<r>Guard_def
  by clarsimp

paragraph \<open>1-to-2\<close>

lemma [\<phi>reason_template name F.G.norm_src [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' y : r x y @action \<A>_template_reason undefined)
\<Longrightarrow> x \<Ztypecolon> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r' y @action \<A>_transitive_simp \<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Action_Tag_def Tyops_Commute_def Premise_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template name F.G.norm_tgt [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' y : r x y @action \<A>_template_reason undefined)
\<Longrightarrow> x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (G T U) \<s>\<u>\<b>\<j> y. r' y @action \<A>_backward_transitive_simp \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Action_Tag_def Tyops_Commute_def Premise_def Simplify_def \<r>Guard_def
  by clarsimp

paragraph \<open>2-to-1\<close>

lemma [\<phi>reason_template name F.G.norm_src [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' y : r x y @action \<A>_template_reason undefined)
\<Longrightarrow> x \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (G T U) \<s>\<u>\<b>\<j> y. r' y @action \<A>_transitive_simp \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Action_Tag_def Tyops_Commute_def Premise_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template name F.G.norm_tgt [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (\<And>y. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' y : r x y @action \<A>_template_reason undefined)
\<Longrightarrow> x \<Ztypecolon> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F'\<^sub>T T) (F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r' y @action \<A>_backward_transitive_simp \<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Action_Tag_def Tyops_Commute_def Premise_def Simplify_def \<r>Guard_def
  by clarsimp

paragraph \<open>\<open>\<Lambda>\<close>\<close>

lemma [\<phi>reason_template name F.G.norm_src [\<phi>ToA_SA_norm_simp default]]:
  \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>I F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (\<lambda>p. F' (T p)) \<s>\<u>\<b>\<j> y. r x y @action \<A>_transitive_simp \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>I_def Action_Tag_def Tyops_Commute_def Premise_def
  by clarsimp

lemma [\<phi>reason_template name F.G.norm_src [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>\<Lambda>\<^sub>E F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F (\<lambda>p. G (T p)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r x y @action \<A>_transitive_simp \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>E_def Action_Tag_def Tyops_Commute_def Premise_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template name F.G.norm_tgt [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>\<Lambda>\<^sub>I F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (\<lambda>p. F' (T p)) \<s>\<u>\<b>\<j> y. r x y @action \<A>_backward_transitive_simp \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>I_def Action_Tag_def Tyops_Commute_def Premise_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template name F.G.norm_tgt [\<phi>ToA_SA_norm_simp default]]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>\<Lambda>\<^sub>E F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F (\<lambda>p. G (T p)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r x y @action \<A>_backward_transitive_simp \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>E_def Action_Tag_def Tyops_Commute_def Premise_def \<r>Guard_def
  by clarsimp


paragraph \<open>Bubbling\<close>

subparagraph \<open>1-to-1\<close>

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (F' T) \<s>\<u>\<b>\<j> y. r x y @action \<A>simp \<close>
  unfolding Tyops_Commute_def Premise_def Action_Tag_def Bubbling_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F' T) \<s>\<u>\<b>\<j> y. r x y @action \<A>backward_simp\<close>
  unfolding Tyops_Commute_def Premise_def Bubbling_def Transformation_def Action_Tag_def \<r>Guard_def
  by clarsimp


subparagraph \<open>1-to-2\<close>

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (F'\<^sub>T T) (F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r x y @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Action_Tag_def Bubbling_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r x y @action \<A>backward_simp\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Bubbling_def Action_Tag_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r x y @action \<A>backward_simp\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Bubbling_def Action_Tag_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<s>\<u>\<b>\<j> y. r x y @action \<A>backward_simp\<close>
  unfolding Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Bubbling_def Action_Tag_def \<r>Guard_def
  by clarsimp


subparagraph \<open>2-to-1\<close>

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<s>\<u>\<b>\<j> y. r x y @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Action_Tag_def Bubbling_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<s>\<u>\<b>\<j> y. r x y @action \<A>simp
    <except-pattern> x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YYY @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Action_Tag_def Bubbling_def Except_Pattern_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> G' (F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (G T U) \<s>\<u>\<b>\<j> y. r x y @action \<A>simp
    <except-pattern> x \<Ztypecolon> G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> YYY @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Action_Tag_def Bubbling_def Except_Pattern_def Simplify_def \<r>Guard_def
  by clarsimp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 F F'\<^sub>T F'\<^sub>U G G' T U D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (F'\<^sub>T T) (F'\<^sub>U U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T U) \<s>\<u>\<b>\<j> y. r x y @action \<A>backward_simp\<close>
  unfolding Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def Bubbling_def Action_Tag_def \<r>Guard_def
  by clarsimp


subparagraph \<open>1-to-1\<lambda>\<close>

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>I F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (x \<Ztypecolon> F (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> G' (\<lambda>p. F' (T p)) \<s>\<u>\<b>\<j> y. r x y) @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>I_def Premise_def Bubbling_def Action_Tag_def Simplify_def
  by simp

lemma [\<phi>reason_template default %\<phi>simp_derived_bubbling]:
  \<open> Tyops_Commute\<^sub>\<Lambda>\<^sub>E F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> (x \<Ztypecolon> F (\<lambda>p. G (T p)) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r x y) @action \<A>simp \<close>
  unfolding Tyops_Commute\<^sub>\<Lambda>\<^sub>E_def Premise_def Bubbling_def Action_Tag_def Simplify_def
  by simp


paragraph \<open>To-Transformation Interpreter\<close>

lemma [\<phi>reason_template default %To_ToA_derived]:
  \<open> \<g>\<u>\<a>\<r>\<d> Tyops_Commute F F' G G' T D r
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x
\<Longrightarrow> x \<Ztypecolon> F (G T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> G' (F' T) \<s>\<u>\<b>\<j> y. r x y @action to (\<c>\<o>\<m>\<m>\<u>\<t>\<e> F G) \<close>
  unfolding Tyops_Commute_def Premise_def Action_Tag_def Except_Pattern_def Simplify_def \<r>Guard_def
  by clarsimp


section \<open>Property Derivers\<close>

subsubsection \<open>Extension of BNF-FP\<close>

ML_file \<open>library/phi_type_algebra/tools/BNF_fp_sugar_more.ML\<close>
ML_file \<open>library/phi_type_algebra/tools/extended_BNF_info.ML\<close>



subsubsection \<open>Deriver Framework\<close>

consts \<phi>TA_subgoal :: \<open>action \<Rightarrow> action\<close>
       \<phi>TA_ANT :: action \<comment> \<open>Antecedent in the outcome\<close>
       \<phi>TA_conditioned_ToA_template :: action
       \<phi>TA_pure_facts :: action \<comment> \<open>About \<open>\<phi>TA_conditioned_ToA_template\<close> and \<open>\<phi>TA_pure_facts\<close>,
                                    see comments in \<^file>\<open>library/phi_type_algebra/deriver_framework.ML\<close>
                                    ML function \<open>default_reasoning_configure\<close>\<close>
       \<phi>TA_ToA_elim :: action

definition \<open>\<phi>TA_IND_TARGET T = T\<close>

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

lemma mk_ToA_rule_varified:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq x' x \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x' x
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> Q \<and> P\<close>
  unfolding Premise_def Object_Equiv_def Transformation_def
  by clarsimp blast

lemma mk_ToA_rule'_varified:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x' \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> Object_Equiv T eq
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> eq x' x \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> eq x' x
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> Q \<and> P\<close>
  unfolding REMAINS_def Premise_def Object_Equiv_def Transformation_def
  by (cases C; clarsimp; blast)


lemma [fundef_cong]:
  \<open>T x = T' x' \<Longrightarrow> (x \<Ztypecolon> T) = (x' \<Ztypecolon> T')\<close>
  unfolding \<phi>Type_def by simp

lemma \<phi>TA_ind_target_strip:
  \<open> X @action \<phi>TA_subgoal \<A> \<equiv> X @action \<A> \<close>
  unfolding Action_Tag_def .

(*TODO: rename Action_Tag \<longrightarrow> Reasoning_Tag, @action \<rightarrow> @tag*)

lemma \<phi>TA_common_rewr_imp1:
  \<open> Trueprop (Ant \<longrightarrow> X @action \<phi>TA_subgoal A) \<equiv> (Ant \<Longrightarrow> X @action A) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp1_noact:
  \<open> Trueprop (Ant \<longrightarrow> X @action \<phi>TA_subgoal A) \<equiv> (Ant \<Longrightarrow> X) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp1_rev:
  \<open> (Ant \<Longrightarrow> X @action A) \<equiv> Trueprop (Ant \<longrightarrow> X @action A) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp2:
  \<open> Trueprop (Ant \<longrightarrow> C \<longrightarrow> X @action \<phi>TA_subgoal \<A>) \<equiv> (Ant \<Longrightarrow> C \<Longrightarrow> X @action \<A>) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp2':
  \<open> Trueprop (Ant \<longrightarrow> Q \<longrightarrow> P @action \<phi>TA_subgoal \<A>)
 \<equiv> (Ant \<Longrightarrow> Q \<longrightarrow> (P @action \<A>)) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp2_rev:
  \<open> (Ant \<Longrightarrow> C \<Longrightarrow> X @action \<A>) \<equiv> Trueprop (Ant \<longrightarrow> C \<longrightarrow> X @action \<A>) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp2_noact:
  \<open> Trueprop (Ant \<longrightarrow> C \<longrightarrow> X @action \<phi>TA_subgoal A) \<equiv> (Ant \<Longrightarrow> C \<Longrightarrow> X) \<close>
  unfolding Action_Tag_def atomize_imp .

lemma \<phi>TA_common_rewr_imp23':
  \<open> Trueprop (Ant \<longrightarrow> Q1 \<longrightarrow> Q2 \<longrightarrow> P @action \<phi>TA_subgoal \<A>)
 \<equiv> (Ant \<Longrightarrow> Q1 \<Longrightarrow> Q2 \<longrightarrow> (P @action \<A>)) \<close>
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

lemma elim_TA_ANT:
  \<open> ((PROP A \<Longrightarrow> PROP C) \<Longrightarrow> PROP A \<Longrightarrow> PROP B) \<equiv> (PROP A \<Longrightarrow> PROP C \<Longrightarrow> PROP B) \<close>
  apply rule
  subgoal premises prems by (rule prems(1), rule prems(3), rule prems(2))
  subgoal premises prems by (rule prems(1), rule prems(3), rule prems(2), rule prems(3)) .

ML_file \<open>library/phi_type_algebra/deriver_framework.ML\<close>

consts \<phi>deriver_expansion :: mode

\<phi>reasoner_ML \<phi>deriver_expansion %cutting
  (\<open>Premise \<phi>deriver_expansion _\<close> | \<open>Simplify \<phi>deriver_expansion ?X' ?X\<close> )
  = \<open>Phi_Reasoners.wrap (PLPR_Simplifier.simplifier (K Seq.empty)
        Phi_Type_Derivers.equip_expansion_ss0 {fix_vars=true}) o snd\<close>


subsubsection \<open>Extending Property Guessers\<close>

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

definition Guess_Property :: \<open>'property_const \<Rightarrow> variant \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> bool \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where \<open>Guess_Property the_constant_of_the_property_predicate \<comment> \<open>gives which sort of properties we are guessing\<close>
                        variantness_of_the_property
                        original_\<phi>type unfolded_\<phi>type
                        guessed_antecedents guessed_proof_obligation yielded_conditions
          \<equiv> True\<close>
(*
definition Guess_Property :: \<open>'property_const \<Rightarrow> variant \<Rightarrow> 'a BI \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool option \<Rightarrow> bool\<close>
  where \<open>Guess_Property the_constant_of_the_property_predicate
                        variantness_of_the_property
                        unfolded_\<phi>type_definition
                        guessed_antecedents
                        conditions_of_antecedents
                        guessed_conclusion \<comment> \<open>None for the mode guessing antecedents only\<close>
          \<equiv> True\<close>
*)
declare [[
  \<phi>reason_default_pattern \<open>Guess_Property ?PC ?V ?T ?uT _ _ _\<close> \<Rightarrow>
                          \<open>Guess_Property ?PC ?V ?T ?uT _ _ _\<close> (100)
]]

\<phi>reasoner_group \<phi>TA_guesser = (100, [80, 2999]) for \<open>Guess_Property PC V T uT a pa cond\<close>
    \<open>User heuristics overriding or extending the guesser mechanism of \<phi>type derivers.\<close>
 and \<phi>TA_guesser_init = (3000, [3000, 3000]) for \<open>Guess_Property PC V T uT a pa cond\<close> > \<phi>TA_guesser
    \<open>Initializing the Guessing\<close>
 and \<phi>TA_guesser_default = (30, [2, 79]) for \<open>Guess_Property PC V T uT a pa cond\<close> < \<phi>TA_guesser
    \<open>Default rules handling logical connectives\<close>
 and \<phi>TA_guesser_assigning_variant = (2200, [2200,2200]) for \<open>Guess_Property PC V T uT a pa cond\<close>
                                                          in \<phi>TA_guesser and > \<phi>TA_guesser_default
    \<open>Fallbacks using common default rules\<close>
 and \<phi>TA_guesser_fallback = (1,[1,1]) for \<open>Guess_Property PC V T uT a pa cond\<close> < \<phi>TA_guesser_default
    \<open>Fallbacks of Guess_Property\<close>
                
ML_file \<open>library/phi_type_algebra/guess_property.ML\<close>

paragraph \<open>System Rules\<close>

lemma [\<phi>reason default %\<phi>TA_guesser_fallback]:
  \<open>Guess_Property PC V T T' True (\<lambda>_. True) (\<lambda>_. True)\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser_init]:
  \<open>(\<And>x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_T' x) : (x \<Ztypecolon> T) )
\<Longrightarrow> Guess_Property PC V T var_T' a p c
\<Longrightarrow> Guess_Property PC V T var_T' a p c \<close>
  unfolding Guess_Property_def ..

paragraph \<open>Preset\<close>

lemma [\<phi>reason default %\<phi>TA_guesser_default]:
  \<open> Guess_Property PC False T A a p c
\<Longrightarrow> Guess_Property PC False T (\<lambda>x. A x \<s>\<u>\<b>\<j> P x) a p (\<lambda>x. P x \<and> c x) \<close>
  \<open> (\<And>c. Guess_Property PC False T (\<lambda>x. A' x c) (a' c) (p' c) (cond c))
\<Longrightarrow> Guess_Property PC False T (\<lambda>x. ExSet (A' x)) (All a') (\<lambda>x. \<forall>c. p' c x) (\<lambda>x. \<exists>c. cond c x)\<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason default %\<phi>TA_guesser_default]:
  \<open> Guess_Property PC True T A a p c
\<Longrightarrow> Guess_Property PC True T (\<lambda>x. A x \<s>\<u>\<b>\<j> P x) a (\<lambda>x. P x \<and> p x) c \<close>
  \<open> (\<And>c. Guess_Property PC True T (\<lambda>x. A' x c) (a' c) (c' c) (cond c))
\<Longrightarrow> Guess_Property PC True T (\<lambda>x. ExSet (A' x)) (Ex a') (\<lambda>x. \<exists>c. c' c x) (\<lambda>x. \<forall>c. cond c x) \<close>
  unfolding Guess_Property_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open> Guess_Property PC V T A a1 p1 c1
\<Longrightarrow> Guess_Property PC V T B a2 p2 c2
\<Longrightarrow> Guess_Property PC V T (\<lambda>x. A x * B x) (a1 \<and>\<^sub>\<r> a2) (\<lambda>x. p1 x \<and> p2 x) (\<lambda>x. c1 x \<and> c2 x)\<close>
  unfolding Guess_Property_def ..


subsubsection \<open>Simplify Result\<close>

definition Simplify_Result :: \<open>prop \<Rightarrow> prop \<Rightarrow> prop\<close> where \<open>Simplify_Result P Q \<equiv> (PROP P \<Longrightarrow> PROP Q)\<close>

lemma DO_Simplify_Result:
  \<open> PROP P
\<Longrightarrow> PROP Simplify_Result P Q
\<Longrightarrow> \<r>Success
\<Longrightarrow> PROP Q \<close>
  unfolding Simplify_Result_def .

text \<open>Simplifies only naked conditions (in sens of not wrapped by \<open>\<And>\<close> or \<open>\<Longrightarrow>\<close>) but not arbitrary antecedents\<close>

paragraph \<open>Basic Rules\<close>

lemma
  \<open> PROP \<A>EIF' A A'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A' \<Longrightarrow> PROP Simplify_Result (PROP B) (PROP B'))
\<Longrightarrow> PROP Simplify_Result (PROP A \<Longrightarrow> PROP B) (PROP A \<Longrightarrow> PROP B') \<close>
  unfolding Simplify_Result_def Premise_def \<A>EIF'_def
  subgoal premises prems
    by (rule prems(2), rule prems(1), rule prems(4), rule prems(3), rule prems(4)) .
    



subsubsection \<open>Warn if the Def contains Sat\<close>

\<phi>property_deriver Warn_if_contains_Sat 10 = \<open>fn (quiet, _) => fn [] => fn _ => fn phi => fn thy => (
  if Phi_Syntax.is_Type_Opr (Term.fastype_of (#term phi)) andalso
     Phi_Type.def_contains_satisfaction phi andalso
     not quiet
  then warning ("The \<phi>-type definition contains satisfaction operator (\<Turnstile>).\n\
                \When a \<phi>-type is specified by satisfaction in a boolean assertion, it looses the ability to guide the reasoning.\n\
                \The deriving may fail. It is recommended to use composition operator (\<Zcomp>) to replace the (\<Turnstile>) if possible.")
  else () ;
  thy
)\<close>

subsubsection \<open>Meta Deriver for Pure Syntactical Properties\<close>

ML_file \<open>library/phi_type_algebra/gen_pure_synt_rules.ML\<close>

\<phi>property_deriver Semimodule_No_SDistr 100
    = \<open>Phi_Type_Derivers.meta_Synt_Deriver
          ("Semimodule_No_SDistr",
           @{lemma' \<open>Semimodule_No_SDistr F\<close> by (simp add: Semimodule_No_SDistr_def)},
           SOME (@{reasoner_group %Semimodule_No_SDistr})) \<close>


subsubsection \<open>Abstract Domain\<close>

context begin

private lemma \<phi>TA_Inh_rule:
  \<open> (\<And>x. Ant \<Longrightarrow> (x \<Ztypecolon> OPEN undefined T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P x) @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Abstract_Domain T P\<close>
  unfolding Action_Tag_def Abstract_Domain_def OPEN_def \<r>EIF_def
  by simp

private lemma \<phi>TA_SuC_rule:
  \<open> (\<And>x. Ant \<Longrightarrow> (P x \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> MAKE undefined T) @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Abstract_Domain\<^sub>L T P\<close>
  unfolding Action_Tag_def Abstract_Domain\<^sub>L_def MAKE_def \<r>ESC_def
  by simp

private lemma \<phi>TA_Inh_step:
  \<open> Inh \<i>\<m>\<p>\<l>\<i>\<e>\<s> Any
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (Any \<longrightarrow> P)
\<Longrightarrow> Inh \<i>\<m>\<p>\<l>\<i>\<e>\<s> P \<close>
  unfolding Action_Tag_def Premise_def \<r>EIF_def
  by blast

private lemma \<phi>TA_Suc_step:
  \<open> Any \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> Inh
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (P \<longrightarrow> Any)
\<Longrightarrow> P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> Inh \<close>
  unfolding Action_Tag_def Premise_def \<r>ESC_def
  by blast

private lemma \<phi>TA_Inh_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> (x \<Ztypecolon> OPEN undefined T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P) @action \<phi>TA_subgoal A)
 \<equiv> (Ant \<Longrightarrow> (x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P)) \<close>
  unfolding Action_Tag_def atomize_imp OPEN_def .

private lemma \<phi>TA_Suc_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> (P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> MAKE undefined T) @action \<phi>TA_subgoal A)
 \<equiv> (Ant \<Longrightarrow> (P \<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s> x \<Ztypecolon> MAKE undefined T)) \<close>
  unfolding Action_Tag_def atomize_imp OPEN_def .


ML_file \<open>library/phi_type_algebra/implication.ML\<close>

end

(*hide_fact \<phi>TA_Inh_rule \<phi>TA_Inh_rewr \<phi>TA_Inh_step*)

\<phi>property_deriver Abstract_Domain\<^sub>L 89 for ( \<open>Abstract_Domain\<^sub>L _ _\<close> ) = \<open>
  Phi_Type_Derivers.abstract_domain_L
\<close>

\<phi>property_deriver Abstract_Domain 90 for ( \<open>Abstract_Domain _ _\<close> )
  requires Abstract_Domain\<^sub>L ? = \<open>
  Phi_Type_Derivers.abstract_domain
\<close>



subsubsection \<open>Identity Element Intro \& Elim\<close>

context begin

private lemma \<phi>TA_1L_rule:
  \<open> (\<And>x. Ant \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> OPEN undefined T) (P x) @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Identity_Elements\<^sub>I T D P \<close>
  unfolding Action_Tag_def Identity_Elements\<^sub>I_def OPEN_def
  by blast

private lemma \<phi>TA_1R_rule:
  \<open> (\<And>x. Ant \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> MAKE undefined T) @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Identity_Elements\<^sub>E T D\<close>
  unfolding Action_Tag_def Identity_Elements\<^sub>E_def MAKE_def
  by blast

private lemma \<phi>TA_Ident_I_rule_step:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> A \<Longrightarrow> Identity_Element\<^sub>I X Q)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (A \<longrightarrow> Q \<longrightarrow> P)
\<Longrightarrow> Identity_Element\<^sub>I X P \<close>
  unfolding Identity_Element\<^sub>I_def Premise_def Action_Tag_def Transformation_def Inhabited_def \<r>EIF_def
  by (clarsimp, blast)

(* not enabled, DO NOT REMOVE, I am a bit of hesitate
lemma \<phi>TA_1I_simp:
  \<open> Identity_Elements\<^sub>I T D P
\<Longrightarrow> Abstract_Domain T Q
\<Longrightarrow> (\<And>x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Q x \<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> D' x : D x)
\<Longrightarrow> (\<And>x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> P' x : P x)
\<Longrightarrow> Identity_Elements\<^sub>I T D' P' \<close>
  unfolding Identity_Elements\<^sub>I_def Premise_def Simplify_def Abstract_Domain_def Identity_Element\<^sub>I_def
            Action_Tag_def Transformation_def Inhabited_def
  by clarsimp blast*)

ML_file \<open>library/phi_type_algebra/identity_element.ML\<close>

end


\<phi>property_deriver Identity_Elements\<^sub>I 101 for (\<open>Identity_Elements\<^sub>I _ _ _\<close>)
  = \<open>Phi_Type_Derivers.identity_element_I\<close>

\<phi>property_deriver Identity_Elements\<^sub>E 102 for (\<open>Identity_Elements\<^sub>E _ _\<close>)
  = \<open>Phi_Type_Derivers.identity_element_E\<close>

\<phi>property_deriver Identity_Element_Properties\<^sub>I 103
  = \<open>fn (_, pos) => (K (Phi_Type_Derivers.id_ele_properties pos true))\<close>

\<phi>property_deriver Identity_Element_Properties\<^sub>E 103
  = \<open>fn (_, pos) =>  (K (Phi_Type_Derivers.id_ele_properties pos false))\<close>

\<phi>property_deriver Identity_Element_Properties 104
  requires Identity_Element_Properties\<^sub>I and Identity_Element_Properties\<^sub>E

\<phi>property_deriver Identity_Elements 105
  requires Identity_Elements\<^sub>I and Identity_Elements\<^sub>E and Identity_Element_Properties


paragraph \<open>Guessing Antecedents\<close>


subsubsection \<open>Object Equivalence\<close>

context begin

private lemma Object_Equiv_rule:
  \<open> \<r>EIF Ant Ant'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>x. eq x x))
\<Longrightarrow> (\<And>x y. Ant \<Longrightarrow> eq x y \<Longrightarrow> (x \<Ztypecolon> OPEN undefined T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined T) @action \<phi>TA_subgoal undefined)
              \<comment> \<open>Induct over \<open>x \<Ztypecolon> T\<close>. When \<open>x\<close> is inductively split, the constraint of \<open>eq x y\<close>
                  should also split \<open>y\<close>, so that \<open>y \<Ztypecolon> T\<close> can reduce.
                  A deficiency is, when the relation \<open>eq\<close> is trivially true such as that when
                   \<open>T = List \<circle>\<close>, \<close>
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Object_Equiv T eq \<close>
  unfolding Object_Equiv_def Premise_def Action_Tag_def MAKE_def OPEN_def \<r>EIF_def
  by blast

private lemma \<phi>TA_OE_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>y. P y \<longrightarrow> (x \<Ztypecolon> OPEN undefined T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f y \<Ztypecolon> MAKE undefined U)) @action \<phi>TA_subgoal undefined)
\<equiv> (\<And>y. Ant \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P y \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f y \<Ztypecolon> \<phi>TA_IND_TARGET U @action \<phi>TA_ToA_elim)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all Premise_def OPEN_def MAKE_def
            \<phi>TA_IND_TARGET_def
  by (rule; blast)


private lemma \<phi>TA_OE_rewr_pre:
  \<open> (\<And>y. Ant \<Longrightarrow> P y \<Longrightarrow> C y @action \<A>)
 \<equiv> Trueprop (Ant \<longrightarrow> (\<forall>y. P y \<longrightarrow> C y) @action \<A>) \<close>
  unfolding Action_Tag_def atomize_imp atomize_all
  by (rule; blast)

private lemma \<phi>TA_OE_rewr_CL:
  \<open> Trueprop (Ant \<longrightarrow> (\<forall>y. C y \<longrightarrow> X y) @action \<A>)
 \<equiv> (\<And>y. Ant \<Longrightarrow> C y \<Longrightarrow> X y) \<close>
  unfolding Action_Tag_def atomize_imp atomize_all Premise_def OPEN_def MAKE_def
  by (rule; blast)

lemma ex_pure_imp:
  \<open> (\<exists>x. P x \<Longrightarrow> PROP Q) \<equiv> (\<And>x. P x \<Longrightarrow> PROP Q) \<close>
proof
  fix x
  assume A: \<open>\<exists>x. P x \<Longrightarrow> PROP Q\<close>
     and B: \<open>P x\<close>
  from B have \<open>\<exists>x. P x\<close> by blast
  from A[OF this] show \<open>PROP Q\<close> .
next
  assume A: \<open>\<And>x. P x \<Longrightarrow> PROP Q\<close>
     and B: \<open>\<exists>x. P x\<close>
  from B have \<open>P (@x. P x)\<close> by (simp add: someI_ex) 
  from A[OF this] show \<open>PROP Q\<close> .
qed



private lemma \<phi>TA_OE_rewr:
  \<open>Trueprop (\<forall>y. P y \<longrightarrow> Q y) \<equiv> (\<And>y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P y \<Longrightarrow> Q y)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all Premise_def
  by (rule; blast)

private lemma \<phi>TA_OE_rewr':
  \<open>Trueprop (\<forall>y. P y \<longrightarrow> Q y) \<equiv> (\<And>y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P y \<Longrightarrow> Q y)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all Premise_def
  by (rule; blast)

private lemma \<phi>TA_OE_simp:
  \<open> Object_Equiv T eq
\<Longrightarrow> Abstract_Domain T D
\<Longrightarrow> (\<And>x y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x \<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> eq' x y : eq x y)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> ((\<forall>x. eq x x) \<longrightarrow> (\<forall>x. eq' x x))
\<Longrightarrow> Object_Equiv T eq' \<close>
  unfolding Object_Equiv_def Transformation_def Simplify_def Premise_def
            Abstract_Domain_def Action_Tag_def Inhabited_def \<r>EIF_def
  by clarsimp blast

ML_file \<open>library/phi_type_algebra/object_equiv.ML\<close>

end

(*
\<phi>property_deriver Object_Equiv\<^sub>O 104
  = \<open>Phi_Type_Derivers.object_equiv_singular\<close>
*)
\<phi>property_deriver Object_Equiv 105 for (\<open>Object_Equiv _ _\<close>)
  = \<open>Phi_Type_Derivers.object_equiv\<close>


subsubsection \<open>Functionality\<close>

context begin

private lemma \<phi>TA_IsFunc_rule:
  \<open> (\<And>x. Ant \<Longrightarrow>
         \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P x \<Longrightarrow>
         Is_Functional (x \<Ztypecolon> OPEN undefined T) @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Functionality T P \<close>
  unfolding Action_Tag_def Functionality_def Is_Functional_def Premise_def OPEN_def
  by clarsimp

private lemma \<phi>TA_IsFunc_cong:
  \<open> P \<equiv> P'
\<Longrightarrow> Functionality T P \<equiv> Functionality T P' \<close>
  by simp

private lemma \<phi>TA_IsFunc_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> C \<longrightarrow> Is_Functional (x \<Ztypecolon> OPEN undefined T) @action \<phi>TA_subgoal A)
 \<equiv> (Ant \<Longrightarrow> C \<Longrightarrow> Is_Functional (x \<Ztypecolon> T)) \<close>
  unfolding Action_Tag_def atomize_imp OPEN_def .

ML_file \<open>library/phi_type_algebra/is_functional.ML\<close>

end

\<phi>property_deriver Functionality 100 for (\<open>Functionality _ _\<close>)
    = \<open> Phi_Type_Derivers.is_functional \<close>


subsubsection \<open>Carrier Set\<close>

context begin

private lemma \<phi>TA_CarS_rule:
  \<open> (\<And>x. Ant \<Longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> P x \<Longrightarrow>
          Within_Carrier_Set (x \<Ztypecolon> OPEN undefined T) @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Carrier_Set T P \<close>
  unfolding Carrier_Set_def Action_Tag_def Premise_def OPEN_def
  by clarsimp

private lemma \<phi>TA_CarS_cong:
  \<open> P \<equiv> P'
\<Longrightarrow> Carrier_Set T P \<equiv> Carrier_Set T P' \<close>
  by simp

private lemma \<phi>TA_CarS_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> C \<longrightarrow> Within_Carrier_Set (x \<Ztypecolon> OPEN undefined T) @action \<phi>TA_subgoal A)
 \<equiv> (Ant \<Longrightarrow> C \<Longrightarrow> Within_Carrier_Set (x \<Ztypecolon> T)) \<close>
  unfolding Action_Tag_def atomize_imp OPEN_def .

ML_file \<open>library/phi_type_algebra/carrier_set.ML\<close>

end

\<phi>property_deriver Carrier_Set 100 for (\<open>Carrier_Set _ _\<close>)
    = \<open> Phi_Type_Derivers.carrier_set \<close>

\<phi>property_deriver Basic 109
  requires Object_Equiv and Abstract_Domain and Carrier_Set ?


subsubsection \<open>Transformation Functor\<close>

context begin

private lemma \<phi>TA_TF_rule:
  \<open>(\<And>g x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D x \<and> g a b \<longrightarrow> b \<in> R x) \<Longrightarrow>
              Ant \<Longrightarrow>
              (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D x \<Longrightarrow> a \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U \<s>\<u>\<b>\<j> b. g a b @action to U) \<Longrightarrow> \<comment> \<open>split D\<close>
              (x \<Ztypecolon> OPEN undefined (F1 T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined (F2 U) \<s>\<u>\<b>\<j> y. mapper g x y) @action \<phi>TA_subgoal (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> U)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Transformation_Functor F1 F2 T U D R mapper\<close>
  unfolding Transformation_Functor_def Action_Tag_def Ball_def Premise_def
            OPEN_def MAKE_def
  by simp

private lemma \<phi>TA_TF_deriver_cong:
  \<open> D \<equiv> D'
\<Longrightarrow> (\<And>x. \<exists>a. a \<in> D' x \<Longrightarrow> R x \<equiv> R' x)
\<Longrightarrow> (\<And>g x y. Inhabited (x \<Ztypecolon> F1 T) \<Longrightarrow> Inhabited (y \<Ztypecolon> F2 U) \<Longrightarrow> m g x y \<equiv> m' g x y)
\<Longrightarrow> Transformation_Functor F1 F2 T U D R m \<equiv> Transformation_Functor F1 F2 T U D' R' m' \<close>
  unfolding Transformation_Functor_def atomize_eq Transformation_def Inhabited_def
  by clarsimp blast

(*
lemma \<phi>TA_TF_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x. P x \<longrightarrow> A2 x) \<longrightarrow> C @action \<phi>TA_subgoal (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> U)))
\<equiv> (Ant \<Longrightarrow> (\<And>x. P x \<Longrightarrow> A2 x @action to U) \<Longrightarrow> C @action to U)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .
*)

private lemma \<phi>TA_TF_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x. P x \<longrightarrow> A2 x) \<longrightarrow> C @action \<phi>TA_subgoal \<A>)
\<equiv> (Ant \<Longrightarrow> (\<And>x. P x \<Longrightarrow> A2 x) \<Longrightarrow> C @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .

private lemma \<phi>TA_TF_rewr_pre:
  \<open>(Ant \<Longrightarrow> (\<And>x. P x \<Longrightarrow> A2 x) \<Longrightarrow> C @action \<A>)
 \<equiv> Trueprop (Ant \<longrightarrow> (\<forall>x. P x \<longrightarrow> A2 x) \<longrightarrow> C @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .

paragraph \<open>Bi-Functor\<close>

private lemma \<phi>TA_biTF_rule:
  \<open>(\<And>g\<^sub>1 g\<^sub>2 x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>a b. a \<in> D\<^sub>1 x \<and> g\<^sub>1 a b \<longrightarrow> b \<in> R\<^sub>1 x) \<and> (\<forall>a b. a \<in> D\<^sub>2 x \<and> g\<^sub>2 a b \<longrightarrow> b \<in> R\<^sub>2 x) \<Longrightarrow>
              Ant \<Longrightarrow>
              (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D\<^sub>1 x \<Longrightarrow> a \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>1 \<s>\<u>\<b>\<j> b. g\<^sub>1 a b @action to U\<^sub>1) \<Longrightarrow> \<comment> \<open>split D\<close>
              (\<And>a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D\<^sub>2 x \<Longrightarrow> a \<Ztypecolon> T\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U\<^sub>2 \<s>\<u>\<b>\<j> b. g\<^sub>2 a b @action to U\<^sub>2) \<Longrightarrow> \<comment> \<open>split D\<close>
              (x \<Ztypecolon> OPEN undefined (F1 T\<^sub>1 T\<^sub>2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined (F2 U\<^sub>1 U\<^sub>2) \<s>\<u>\<b>\<j> y. mapper g\<^sub>1 g\<^sub>2 x y)
              @action \<phi>TA_subgoal (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T\<^sub>1 \<Rightarrow> U\<^sub>1 \<o>\<r>\<e>\<l>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T\<^sub>2 \<Rightarrow> U\<^sub>2)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper\<close>
  unfolding Transformation_BiFunctor_def Action_Tag_def Ball_def Premise_def
            OPEN_def MAKE_def
  by simp

private lemma \<phi>TA_biTF_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x. P1 x \<longrightarrow> A1 x) \<longrightarrow> (\<forall>x. P2 x \<longrightarrow> A2 x) \<longrightarrow> C @action \<phi>TA_subgoal \<A>)
\<equiv> (Ant \<Longrightarrow> (\<And>x. P1 x \<Longrightarrow> A1 x) \<Longrightarrow> (\<And>x. P2 x \<Longrightarrow> A2 x) \<Longrightarrow> C @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .

private lemma \<phi>TA_biTF_rewr_pre:
  \<open>(Ant \<Longrightarrow> (\<And>x. P1 x \<Longrightarrow> A1 x) \<Longrightarrow> (\<And>x. P2 x \<Longrightarrow> A2 x) \<Longrightarrow> C @action \<A>)
 \<equiv> Trueprop (Ant \<longrightarrow> (\<forall>x. P1 x \<longrightarrow> A1 x) \<longrightarrow> (\<forall>x. P2 x \<longrightarrow> A2 x) \<longrightarrow> C @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .

private lemma \<phi>TA_biTF_deriver_cong:
  \<open> D\<^sub>1 \<equiv> D'\<^sub>1
\<Longrightarrow> D\<^sub>2 \<equiv> D'\<^sub>2
\<Longrightarrow> (\<And>x. \<exists>a. a \<in> D'\<^sub>1 x \<Longrightarrow> R\<^sub>1 x \<equiv> R'\<^sub>1 x)
\<Longrightarrow> (\<And>x. \<exists>a. a \<in> D'\<^sub>2 x \<Longrightarrow> R\<^sub>2 x \<equiv> R'\<^sub>2 x)
\<Longrightarrow> (\<And>g\<^sub>1 g\<^sub>2 x y. Inhabited (x \<Ztypecolon> F1 T\<^sub>1 T\<^sub>2) \<Longrightarrow> Inhabited (y \<Ztypecolon> F2 U\<^sub>1 U\<^sub>2) \<Longrightarrow> m g\<^sub>1 g\<^sub>2 x y \<equiv> m' g\<^sub>1 g\<^sub>2 x y)
\<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 m
 \<equiv> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D'\<^sub>1 D'\<^sub>2 R'\<^sub>1 R'\<^sub>2 m' \<close>
  unfolding Transformation_BiFunctor_def atomize_eq Transformation_def Inhabited_def
  by clarsimp (smt (verit, ccfv_threshold))

paragraph \<open>Parameterization\<close>

private lemma \<phi>TA_TF\<^sub>\<Lambda>_rule:
  \<open> (\<And>g x. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> (\<forall>p a b. a \<in> D p x \<and> g p a b \<longrightarrow> b \<in> R p x) \<Longrightarrow>
              Ant \<Longrightarrow>
              (\<And>p a. \<p>\<r>\<e>\<m>\<i>\<s>\<e> a \<in> D p x \<Longrightarrow> a \<Ztypecolon> T p \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> U p \<s>\<u>\<b>\<j> b. g p a b @action to (U p)) \<Longrightarrow> \<comment> \<open>split D\<close>
              (x \<Ztypecolon> MAKE undefined (F1 T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> OPEN undefined (F2 U) \<s>\<u>\<b>\<j> y. mapper g x y) @action \<phi>TA_subgoal (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> T \<Rightarrow> U)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R mapper \<close>
  unfolding Transformation_Functor\<^sub>\<Lambda>_def Action_Tag_def Ball_def Premise_def
            OPEN_def MAKE_def
  by clarsimp

private lemma \<phi>TA_TF\<^sub>\<Lambda>_deriver_cong:
  \<open> D \<equiv> D'
\<Longrightarrow> (\<And>p x. \<exists>a. a \<in> D' p x \<Longrightarrow> R p x \<equiv> R' p x)
\<Longrightarrow> (\<And>g x y. Inhabited (x \<Ztypecolon> F1 T) \<Longrightarrow> Inhabited (y \<Ztypecolon> F2 U) \<Longrightarrow> m g x y \<equiv> m' g x y)
\<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R m \<equiv> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D' R' m' \<close>
  unfolding Transformation_Functor\<^sub>\<Lambda>_def atomize_eq Transformation_def Inhabited_def
  by clarsimp blast

private lemma \<phi>TA_TF\<^sub>\<Lambda>_rewr_C:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>p x. P p x \<longrightarrow> A2 p x) \<longrightarrow> C @action \<phi>TA_subgoal \<A>)
\<equiv> (Ant \<Longrightarrow> (\<And>p x. P p x \<Longrightarrow> A2 p x) \<Longrightarrow> C @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .

private lemma \<phi>TA_TF\<^sub>\<Lambda>_rewr_pre:
  \<open>(Ant \<Longrightarrow> (\<And>p x. P p x \<Longrightarrow> A2 p x) \<Longrightarrow> C @action \<A>)
 \<equiv> Trueprop (Ant \<longrightarrow> (\<forall>p x. P p x \<longrightarrow> A2 p x) \<longrightarrow> C @action \<A>)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all .


subsubsection \<open>Functional Transformation Functor\<close>

paragraph \<open>Functor\<close>

private lemma \<phi>TA_FTF_rule:
  \<open> \<r>EIF Ant Ant'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> Transformation_Functor F1 F2 T U D R mapper)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> Object_Equiv (F2 U) eq)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>f P x y. mapper (\<lambda>a b. b = f a \<and> P a) x y \<longrightarrow> eq y (fm f P x) \<and> pm f P x))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Functional_Transformation_Functor F1 F2 T U D R pm fm\<close>
  unfolding Premise_def fun_eq_iff Action_Tag_def \<r>EIF_def
  using infer_FTF_from_FT
  by blast

private lemma \<phi>TA_FTF_deriver_cong:
  \<open> D \<equiv> D'
\<Longrightarrow> (\<And>x. \<exists>a. a \<in> D' x \<Longrightarrow> R x \<equiv> R' x)
\<Longrightarrow> (\<And>f P x. Inhabited (x \<Ztypecolon> F1 T) \<Longrightarrow> fm f P x \<equiv> fm' f P x)
\<Longrightarrow> (\<And>f P x. Inhabited (x \<Ztypecolon> F1 T) \<Longrightarrow> Inhabited (fm' f P x \<Ztypecolon> F2 U) \<Longrightarrow> pm f P x \<equiv> pm' f P x)
\<Longrightarrow> Functional_Transformation_Functor F1 F2 T U D R pm fm \<equiv>
    Functional_Transformation_Functor F1 F2 T U D' R' pm' fm' \<close>
  unfolding Functional_Transformation_Functor_def atomize_eq Transformation_def Inhabited_def
  by (clarsimp, smt (verit, best))

paragraph \<open>Bi-Functor\<close>

private lemma \<phi>TA_biFTF_rule:
  \<open> \<r>EIF Ant Ant'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 mapper)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> Object_Equiv (F2 U\<^sub>1 U\<^sub>2) eq)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x y. mapper (\<lambda>a b. b = f\<^sub>1 a \<and> P\<^sub>1 a) (\<lambda>a b. b = f\<^sub>2 a \<and> P\<^sub>2 a) x y
                                  \<longrightarrow> eq y (fm f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x) \<and> pm f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Functional_Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 pm fm\<close>
  unfolding Premise_def fun_eq_iff Action_Tag_def \<r>EIF_def
  using infer_biFTF_from_biFT
  by blast

private lemma \<phi>TA_biFTF_deriver_cong:
  \<open> D\<^sub>1 \<equiv> D'\<^sub>1
\<Longrightarrow> D\<^sub>2 \<equiv> D'\<^sub>2
\<Longrightarrow> (\<And>x. \<exists>a. a \<in> D'\<^sub>1 x \<Longrightarrow> R\<^sub>1 x \<equiv> R'\<^sub>1 x)
\<Longrightarrow> (\<And>x. \<exists>a. a \<in> D'\<^sub>2 x \<Longrightarrow> R\<^sub>2 x \<equiv> R'\<^sub>2 x)
\<Longrightarrow> (\<And>f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x. Inhabited (x \<Ztypecolon> F1 T\<^sub>1 T\<^sub>2) \<Longrightarrow> fm f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x \<equiv> fm' f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x)
\<Longrightarrow> (\<And>f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x. Inhabited (x \<Ztypecolon> F1 T\<^sub>1 T\<^sub>2) \<Longrightarrow> Inhabited (fm' f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x \<Ztypecolon> F2 U\<^sub>1 U\<^sub>2) \<Longrightarrow> pm f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x \<equiv> pm' f\<^sub>1 f\<^sub>2 P\<^sub>1 P\<^sub>2 x)
\<Longrightarrow> Functional_Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D\<^sub>1 D\<^sub>2 R\<^sub>1 R\<^sub>2 pm fm \<equiv>
    Functional_Transformation_BiFunctor F1 F2 T\<^sub>1 T\<^sub>2 U\<^sub>1 U\<^sub>2 D'\<^sub>1 D'\<^sub>2 R'\<^sub>1 R'\<^sub>2 pm' fm' \<close>
  unfolding Functional_Transformation_BiFunctor_def atomize_eq Transformation_def Inhabited_def
  by (clarsimp, smt (verit, best))

paragraph \<open>Parameterization\<close>

private lemma \<phi>TA_FTF\<^sub>\<Lambda>_rule:
  \<open> \<r>EIF Ant Ant'
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R mapper)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> Abstract_Domain (F1 T) P\<^sub>T)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> Abstract_Domain (F2 U) P\<^sub>U)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> Object_Equiv (F2 U) eq)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ant' \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (\<forall>f P x y. P\<^sub>T x \<and> P\<^sub>U y \<and> mapper (\<lambda>p a b. b = f p a \<and> P p a) x y \<longrightarrow> eq y (fm f P x) \<and> pm f P x))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R pm fm \<close>
  unfolding Premise_def Action_Tag_def \<r>EIF_def
  using infer_FTF\<^sub>\<Lambda>_from_FT\<^sub>\<Lambda> by blast

private lemma \<phi>TA_FTF\<^sub>\<Lambda>_deriver_cong:
  \<open> D \<equiv> D'
\<Longrightarrow> (\<And>p x. \<exists>a. a \<in> D' p x \<Longrightarrow> R p x \<equiv> R' p x)
\<Longrightarrow> (\<And>f P x. Inhabited (x \<Ztypecolon> F1 T) \<Longrightarrow> fm f P x \<equiv> fm' f P x)
\<Longrightarrow> (\<And>f P x. Inhabited (x \<Ztypecolon> F1 T) \<Longrightarrow> Inhabited (fm' f P x \<Ztypecolon> F2 U) \<Longrightarrow> pm f P x \<equiv> pm' f P x)
\<Longrightarrow> Functional_Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D R pm fm \<equiv>
    Functional_Transformation_Functor\<^sub>\<Lambda> F1 F2 T U D' R' pm' fm' \<close>
  unfolding Functional_Transformation_Functor\<^sub>\<Lambda>_def atomize_eq Transformation_def Inhabited_def
  by (clarsimp, smt (verit, del_insts))


ML_file \<open>library/phi_type_algebra/transformation_functor.ML\<close>

end

\<phi>property_deriver Transformation_Functor 110
    for ( \<open>Transformation_Functor _ _ _ _ _ _ _\<close>
        | \<open>Transformation_BiFunctor _ _ _ _ _ _ _ _ _ _ _\<close>
        | \<open>Transformation_Functor\<^sub>\<Lambda> _ _ _ _ _ _ _\<close>)
  = \<open> Phi_Type_Derivers.transformation_functor \<close>

\<phi>property_deriver Functional_Transformation_Functor 111
  for ( \<open>Functional_Transformation_Functor _ _ _ _ _ _ _ _\<close>
      | \<open>Functional_Transformation_BiFunctor _ _ _ _ _ _ _ _ _ _ _ _\<close>
      | \<open>Functional_Transformation_Functor\<^sub>\<Lambda> _ _ _ _ _ _ _ _\<close>)
  requires Transformation_Functor
    = \<open>Phi_Type_Derivers.functional_transformation_functor\<close>


subsubsection \<open>Separation Homo\<close>

text \<open>Note, as an instance of Commutativity of Type Operators, the names of \<open>introduction rule\<close>
  and \<open>elimination rule\<close> are just reversed. It is intentional, because I really think those names
  are more natural and we don't really have to force the consistency of the names between the two levels.\<close>

context begin

paragraph \<open>Normal\<close>

private lemma \<phi>TA_SH\<^sub>I_rule:
  \<open> (\<And>z. Ant \<Longrightarrow>
            (\<forall>x y. (x,y) \<in> D \<and> w(x,y) = z
                \<longrightarrow> ((y \<Ztypecolon> OPEN undefined (Fb U)) * (x \<Ztypecolon> OPEN undefined (Fa T))
                    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> MAKE undefined (Fc (T \<^emph> U)))) @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Separation_Homo\<^sub>I Fa Fb Fc T U D w \<close>
  unfolding Separation_Homo\<^sub>I_def \<phi>Prod_expn' Action_Tag_def MAKE_def OPEN_def
  by simp

private lemma \<phi>TA_SH\<^sub>E_rule:
  \<open> (\<And>z. Ant \<Longrightarrow> (z \<Ztypecolon> OPEN undefined (Fc (T \<^emph>\<^sub>\<A> U))
                  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz z \<Ztypecolon> NO_SIMP \<phi>Prod (MAKE undefined (Ft T)) (MAKE undefined (Fu U))) @action \<phi>TA_subgoal \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U uz \<close>
  unfolding Separation_Homo\<^sub>E_def \<phi>Prod_expn' Action_Tag_def Bubbling_def MAKE_def OPEN_def NO_SIMP_def
  by simp

private lemma \<phi>TA_SH\<^sub>I_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (\<forall>x y. P x y \<longrightarrow> ((y \<Ztypecolon> OPEN undefined Tb) * (x \<Ztypecolon> OPEN undefined Ta)
                                      \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> MAKE undefined Tc)) @action \<phi>TA_subgoal undefined)
\<equiv> (\<And>x y. Ant @action \<phi>TA_ANT \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> P x y \<Longrightarrow> ((y \<Ztypecolon> Tb) * (x \<Ztypecolon> Ta) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> Tc) @action \<phi>TA_ToA_elim)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all Premise_def OPEN_def MAKE_def
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

private lemma \<phi>TA_SH\<^sub>E_rewr_IH:
  \<open>Trueprop (Ant \<longrightarrow> (z \<Ztypecolon> OPEN undefined T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz \<Ztypecolon> MAKE undefined U1 \<^emph> MAKE undefined U2)
            @action \<phi>TA_subgoal A)
\<equiv> (Ant @action \<phi>TA_ANT \<Longrightarrow> z \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z' \<Ztypecolon> U1 \<^emph> U2 \<s>\<u>\<b>\<j> z'. z' = uz @action A)\<close>
  unfolding Action_Tag_def atomize_imp atomize_all OPEN_def MAKE_def
  by simp

private lemma \<phi>TA_SH\<^sub>I_DV_cong:
  \<open> D \<equiv> D'
\<Longrightarrow> z \<equiv> z'
\<Longrightarrow> Separation_Homo\<^sub>I Ft Fu Fc T U D z \<equiv> Separation_Homo\<^sub>I Ft Fu Fc T U D' z' \<close>
  by simp

private lemma \<phi>TA_SH\<^sub>E_DV_cong:
  \<open> u \<equiv> u'
\<Longrightarrow> Separation_Homo\<^sub>E Ft Fu Fc T U u \<equiv> Separation_Homo\<^sub>E Ft Fu Fc T U u' \<close>
  by simp

paragraph \<open>With Parameterization\<close>

private lemma \<phi>TA_SH\<^sub>\<Lambda>\<^sub>I_rule:
  \<open> (\<And>z. Ant \<Longrightarrow>
            (\<forall>x y. (x,y) \<in> D \<and> w(x,y) = z
                \<longrightarrow> ((y \<Ztypecolon> OPEN undefined (Fb U)) * (x \<Ztypecolon> OPEN undefined (Fa T))
                    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> MAKE undefined (Fc (\<lambda>p. T p \<^emph> U p))))
            @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>I Fa Fb Fc T U D w \<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>I_def \<phi>Prod_expn' Action_Tag_def MAKE_def OPEN_def
  by simp

private lemma \<phi>TA_SH\<^sub>\<Lambda>\<^sub>E_rule:
  \<open> (\<And>z. Ant \<Longrightarrow> (z \<Ztypecolon> OPEN undefined (Fc (\<lambda>p. T p \<^emph>\<^sub>\<A> U p))
                  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz z \<Ztypecolon> NO_SIMP \<phi>Prod (MAKE undefined (Ft T)) (MAKE undefined (Fu U)))
          @action \<phi>TA_subgoal \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E Ft Fu Fc T U uz \<close>
  unfolding Separation_Homo\<^sub>\<Lambda>\<^sub>E_def \<phi>Prod_expn' Action_Tag_def Bubbling_def
            MAKE_def OPEN_def NO_SIMP_def
  by simp

private lemma \<phi>TA_SH\<^sub>\<Lambda>\<^sub>I_DV_cong:
  \<open> D \<equiv> D'
\<Longrightarrow> z \<equiv> z'
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>I Ft Fu Fc T U D z \<equiv> Separation_Homo\<^sub>\<Lambda>\<^sub>I Ft Fu Fc T U D' z' \<close>
  by simp

private lemma \<phi>TA_SH\<^sub>\<Lambda>\<^sub>E_DV_cong:
  \<open> u \<equiv> u'
\<Longrightarrow> Separation_Homo\<^sub>\<Lambda>\<^sub>E Ft Fu Fc T U u \<equiv> Separation_Homo\<^sub>\<Lambda>\<^sub>E Ft Fu Fc T U u' \<close>
  by simp

private lemma \<phi>TA_SH\<^sub>E_rewr_pre:
  \<open> (Ant \<Longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> NO_SIMP \<phi>Prod T U) @action \<A>)
\<equiv> Trueprop (Ant \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> T \<^emph> U) @action \<A>) \<close>
  unfolding atomize_imp Action_Tag_def NO_SIMP_def .


ML_file \<open>library/phi_type_algebra/separation_homo.ML\<close>

end

(*
hide_fact \<phi>TA_SH\<^sub>I_rule \<phi>TA_SH\<^sub>E_rule \<phi>TA_SH\<^sub>I_rewr_IH \<phi>TA_SH\<^sub>I_rewr_C
          \<phi>TA_SH\<^sub>E_rewr_IH \<phi>TA_SH\<^sub>E_rewr_C*)

\<phi>property_deriver Separation_Homo\<^sub>I 120
  for (\<open>Separation_Homo\<^sub>I _ _ _ _ _ _ _\<close> | \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>I _ _ _ _ _ _ _\<close>)
    = \<open> Phi_Type_Derivers.separation_homo_I \<close>

\<phi>property_deriver Separation_Homo\<^sub>E 121
  for (\<open>Separation_Homo\<^sub>E _ _ _ _ _ _\<close> | \<open>Separation_Homo\<^sub>\<Lambda>\<^sub>E _ _ _ _ _ _\<close>)
    = \<open> Phi_Type_Derivers.separation_homo_E \<close>

\<phi>property_deriver Separation_Homo 122 requires Separation_Homo\<^sub>I and Separation_Homo\<^sub>E

\<phi>property_deriver Sep_Functor 130 
  requires Separation_Homo
       and Functional_Transformation_Functor
       and Basic
  \<comment> \<open>A separation functor is defined as a transformation functor which is also extendedly commutative
     with separation operator \<open>\<^emph>\<close>. The extended commutativity means existing a pair of function \<open>z,u\<close> with
     \<open>x \<Ztypecolon> F(T) \<^emph> F(U) \<longrightarrow> z x \<Ztypecolon> F(T \<^emph> U)\<close> and \<open>y \<Ztypecolon> F(T \<^emph> U) \<longrightarrow> u y \<Ztypecolon> F(T) \<^emph> F(U)\<close> for any \<open>x,y\<close>, and it degenerates
     to the usual commutativity when \<open>z, u = \<lambda>x. x\<close>.\<close>

\<phi>property_deriver Sep_Functor_1 131
  requires Sep_Functor
       and Identity_Elements
       and Identity_Element_Properties


subsubsection \<open>Congruence in Function Definition\<close>

(*TODO: re-implement by template*)

lemma function_congruence_template:
  \<open> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Transformation_Functor F F' T U D R M)
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Transformation_Functor F' F U T D' R' M')
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Object_Equiv (F' U) eq')
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> x = y \<and> (\<forall>a \<in> D x. T a = U a) \<and> eqs \<Longrightarrow> Object_Equiv (F T) eq)
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (x = y \<and> eqs \<longrightarrow>
              D x \<subseteq> R x \<and> (\<forall>x y. M (=) x y \<longrightarrow> eq' y x) \<and> (\<forall>x. D x = D' x) \<and>
              D' y \<subseteq> R' y \<and> (\<forall>x y. M' (=) y x \<longrightarrow> eq x y))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
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

definition Guess_Scalar_Zero :: \<open> 's itself \<Rightarrow> 'c::one itself \<Rightarrow> 'a itself
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> 's
                              \<Rightarrow> bool \<Rightarrow> bool
                              \<Rightarrow> bool \<close>
  where \<open>Guess_Scalar_Zero _ _ _ F unfolded_F zero ants conds \<equiv> True\<close>

definition Guess_Scalar_One\<^sub>I :: \<open> 's itself \<Rightarrow> 'c\<^sub>T itself \<Rightarrow> 'c itself \<Rightarrow> 'a\<^sub>T itself \<Rightarrow>'a itself
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>
                              \<Rightarrow> ('c,'a\<^sub>1) \<phi>
                              \<Rightarrow> 's \<Rightarrow> ('a\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('a\<^sub>1 \<Rightarrow> 'a) \<Rightarrow> ('a\<^sub>1 \<Rightarrow> bool)
                              \<Rightarrow> bool \<Rightarrow> bool
                              \<Rightarrow> bool \<close>
  where \<open>Guess_Scalar_One\<^sub>I _ _ _ _ _ F unfolded_F T T\<^sub>1 one Dx f P ants conds \<equiv> True\<close>

definition Guess_Scalar_One\<^sub>E :: \<open> 's itself \<Rightarrow> 'c\<^sub>T itself \<Rightarrow> 'c itself \<Rightarrow> 'a\<^sub>T itself => 'a itself
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                              \<Rightarrow> ('c\<^sub>T,'a\<^sub>T) \<phi>
                              \<Rightarrow> ('c,'a\<^sub>1) \<phi>
                              \<Rightarrow> 's \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a\<^sub>1) \<Rightarrow> ('a \<Rightarrow> bool)
                              \<Rightarrow> bool \<Rightarrow> bool
                              \<Rightarrow> bool \<close>
  where \<open>Guess_Scalar_One\<^sub>E _ _ _ _ _ F unfolded_F T T\<^sub>1 one Dx f P ants conds \<equiv> True\<close>

definition Guess_Scalar_Assoc\<^sub>I :: \<open> 's\<^sub>c itself \<Rightarrow> 'c itself \<Rightarrow> 'c\<^sub>s\<^sub>t itself \<Rightarrow> 'a itself \<Rightarrow> 'a\<^sub>s\<^sub>t itself
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
  where \<open>Guess_Scalar_Assoc\<^sub>I _ _ _ _ _ Fs Ft Fc unfolded_Fc T Ds Dt Dx smul f ants conds \<equiv> True\<close>

definition Guess_Scalar_Assoc\<^sub>E :: \<open> 's\<^sub>c itself \<Rightarrow> 'c itself \<Rightarrow> 'c\<^sub>s\<^sub>t itself \<Rightarrow> 'a itself \<Rightarrow> 'a\<^sub>s\<^sub>t itself
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>_\<^sub>t) \<phi>)
                                 \<Rightarrow> ('s\<^sub>t \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>t,'a\<^sub>t) \<phi>)
                                 \<Rightarrow> ('s\<^sub>c \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>t) \<phi>)
                                 \<Rightarrow> ('s\<^sub>c \<Rightarrow> ('c,'a) \<phi> \<Rightarrow> ('c\<^sub>s\<^sub>t,'a\<^sub>s\<^sub>t) \<phi>)
                                 \<Rightarrow> ('c,'a) \<phi>
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> bool)
                                 \<Rightarrow> ('s\<^sub>t \<Rightarrow> bool)
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t \<Rightarrow> bool)
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 's\<^sub>c)
                                 \<Rightarrow> ('s\<^sub>s \<Rightarrow> 's\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>t \<Rightarrow> 'a\<^sub>s\<^sub>_\<^sub>t)
                                 \<Rightarrow> bool \<Rightarrow> bool
                                 \<Rightarrow> bool\<close>
  where \<open>Guess_Scalar_Assoc\<^sub>E _ _ _ _ _ Fs Ft Fc unfolded_Fc T Ds Dt Dx smul f ants conds \<equiv> True\<close>


definition Guess_Zip_of_Semimodule :: \<open>'s itself \<Rightarrow> ('c::sep_magma) itself \<Rightarrow> 'a itself
                                      \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                                      \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                                      \<Rightarrow> ('s \<Rightarrow> bool)
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool)
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a)
                                      \<Rightarrow> bool \<Rightarrow> bool
                                      \<Rightarrow> bool\<close>
  where \<open>Guess_Zip_of_Semimodule type_scalar type_concrete type_abstract
                                 F unfolded_F_def
                                 domain_of_scalar domain_of_abstract zip_opr
                                 antecedents conditions_of_antecedents
       \<equiv> True\<close>

definition Guess_Unzip_of_Semimodule :: \<open>'s itself \<Rightarrow> 'c itself \<Rightarrow> 'a itself
                                      \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                                      \<Rightarrow> ('s \<Rightarrow> ('c,'a) \<phi>)
                                      \<Rightarrow> ('s \<Rightarrow> bool)
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool) 
                                      \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a)
                                      \<Rightarrow> bool \<Rightarrow> bool
                                      \<Rightarrow> bool\<close>
  where \<open>Guess_Unzip_of_Semimodule type_scalar type_concrete type_abstract
                                   F unfolded_typ_def
                                   domain_of_scalar domain_of_abstract unzip_opr
                                   antecedents conditions_of_antecedents
       \<equiv> True\<close>

declare [[ \<phi>reason_default_pattern
      (*\<open>Guess_Scalar_One\<^sub>I ?S ?C ?A\<^sub>T ?A _ ?def ?T _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_One\<^sub>I ?S ?C ?A\<^sub>T ?A _ ?def ?T _ _ _\<close>   (100)
  and*)
      \<open>Guess_Scalar_Zero ?S ?C ?A _ ?def _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_Zero ?S ?C ?A _ ?def _ _ _\<close>   (100)
  and \<open>Guess_Scalar_One\<^sub>I ?S ?C\<^sub>T ?C ?A\<^sub>T ?A _ ?def ?T _ _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_One\<^sub>I ?S ?C\<^sub>T ?C ?A\<^sub>T ?A _ ?def ?T _ _ _ _ _ _ _\<close>   (100)
  and \<open>Guess_Scalar_One\<^sub>E ?S ?C\<^sub>T ?C ?A\<^sub>T ?A _ ?def ?T _ _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_One\<^sub>E ?S ?C\<^sub>T ?C ?A\<^sub>T ?A _ ?def ?T _ _ _ _ _ _ _\<close>   (100)
  and \<open>Guess_Zip_of_Semimodule ?S ?C ?A _ ?def _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Zip_of_Semimodule ?S ?C ?A _ ?def _ _ _ _ _\<close>   (100)
  and \<open>Guess_Unzip_of_Semimodule ?S ?C ?A _ ?def _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Unzip_of_Semimodule ?S ?C ?A _ ?def _ _ _ _ _\<close>   (100)
  and \<open>Guess_Scalar_Assoc\<^sub>I ?S ?C\<^sub>T ?C ?A\<^sub>T ?A\<^sub>F _ _ _ ?def ?T _ _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_Assoc\<^sub>I ?S ?C\<^sub>T ?C ?A\<^sub>T ?A\<^sub>F _ _ _ ?def ?T _ _ _ _ _ _ _\<close>   (100)
  and \<open>Guess_Scalar_Assoc\<^sub>E ?S ?C\<^sub>T ?C ?A\<^sub>T ?A\<^sub>F _ _ _ ?def ?T _ _ _ _ _ _ _\<close> \<Rightarrow>
      \<open>Guess_Scalar_Assoc\<^sub>E ?S ?C\<^sub>T ?C ?A\<^sub>T ?A\<^sub>F _ _ _ ?def ?T _ _ _ _ _ _ _\<close>   (100)
]]

text \<open>Guessing the zip operation of a semimodule is far beyond what can be inferred from BNF,
      partially because a semimodule is over two algebraic sorts (i.e., two logical types).
      Due to this, the guessing of the abstract operators of semimodules more relies on pre-registered
      records over the logical types.\<close>

paragraph \<open>Initialization\<close>

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s x) : (x \<Ztypecolon> F s) )
\<Longrightarrow> Guess_Scalar_Zero TS TC TA F var_unfolded_F z ants conds
\<Longrightarrow> Guess_Scalar_Zero TS TC TA F var_unfolded_F z ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s x) : (x \<Ztypecolon> F s) )
\<Longrightarrow> Guess_Scalar_One\<^sub>I TS TC\<^sub>T TC TA\<^sub>T TA F var_unfolded_F T T\<^sub>1 one Dx f P ants conds
\<Longrightarrow> Guess_Scalar_One\<^sub>I TS TC\<^sub>T TC TA\<^sub>T TA F var_unfolded_F T T\<^sub>1 one Dx f P ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s x) : (x \<Ztypecolon> F s) )
\<Longrightarrow> Guess_Scalar_One\<^sub>E TS TC\<^sub>T TC TA\<^sub>T TA F var_unfolded_F T T\<^sub>1 one Dx f P ants conds
\<Longrightarrow> Guess_Scalar_One\<^sub>E TS TC\<^sub>T TC TA\<^sub>T TA F var_unfolded_F T T\<^sub>1 one Dx f P ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_Fc s T x) : (x \<Ztypecolon> Fc s T) )
\<Longrightarrow> Guess_Scalar_Assoc\<^sub>I TS TC TC' TA\<^sub>T TA Fs Ft Fc var_unfolded_Fc T Ds Dt Dx smul f ants conds
\<Longrightarrow> Guess_Scalar_Assoc\<^sub>I TS TC TC' TA\<^sub>T TA Fs Ft Fc var_unfolded_Fc T Ds Dt Dx smul f ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_Fc s T x) : (x \<Ztypecolon> Fc s T) )
\<Longrightarrow> Guess_Scalar_Assoc\<^sub>E TS TC TC' TA\<^sub>T TA Fs Ft Fc var_unfolded_Fc T Ds Dt Dx smul f ants conds
\<Longrightarrow> Guess_Scalar_Assoc\<^sub>E TS TC TC' TA\<^sub>T TA Fs Ft Fc var_unfolded_Fc T Ds Dt Dx smul f ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s x) : (x \<Ztypecolon> F s) )
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA F var_unfolded_F Ds Dx z ants conds
\<Longrightarrow> Guess_Zip_of_Semimodule TS TC TA F var_unfolded_F Ds Dx z ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init]:
  \<open> (\<And>s x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_F s x) : (x \<Ztypecolon> F s) )
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA F var_unfolded_F Ds Dx z ants conds
\<Longrightarrow> Guess_Unzip_of_Semimodule TS TC TA F var_unfolded_F Ds Dx z ants conds\<close> .


paragraph \<open>Guess_Scalar_Zero\<close>

lemma [\<phi>reason %\<phi>TA_guesser_fallback]:
  \<open>Guess_Scalar_Zero TYPE('s::zero) TYPE('c::one) TYPE('a)
                     F unfolded_F 0 True True \<close>
  unfolding Guess_Scalar_Zero_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_Zero TYPE('s len_intvl) TYPE('c::one) TYPE('a list)
                     F unfolded_F \<lbrakk>x:0\<rwpar> True True\<close>
  unfolding Guess_Scalar_Zero_def ..

paragraph \<open>Guess_Scalar_One\<close>

(* lemma [\<phi>reason %\<phi>TA_guesser_fallback]:
  \<open>Guess_Scalar_One\<^sub>I TYPE('s::one) TYPE('c) TYPE('a) TYPE('a)
                     F whateverT 1 (\<lambda>_. True) (\<lambda>x. x)\<close>
  unfolding Guess_Scalar_One\<^sub>I_def .. *)

lemma [\<phi>reason %\<phi>TA_guesser_fallback]:
  \<open>Guess_Scalar_One\<^sub>I TYPE('s::one) TYPE('c) TYPE('c) TYPE('a) TYPE('a)
                     F whatever T T 1 (\<lambda>_. True) (\<lambda>x. x) (\<lambda>_. True) True True\<close>
  unfolding Guess_Scalar_One\<^sub>I_def ..

lemma [\<phi>reason %\<phi>TA_guesser_fallback]:
  \<open>Guess_Scalar_One\<^sub>E TYPE('s::one) TYPE('c) TYPE('c) TYPE('a) TYPE('a)
                     F whatever T T 1 (\<lambda>_. True) (\<lambda>x. x) (\<lambda>_. True) True True\<close>
  unfolding Guess_Scalar_One\<^sub>E_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_One\<^sub>I TYPE('s len_intvl) TYPE('c) TYPE('c) TYPE('a) TYPE('a list)
                     F whatever T T \<lbrakk>x:1\<rwpar> (\<lambda>_. True) (\<lambda>x. [x]) (\<lambda>_. True) True True\<close>
  unfolding Guess_Scalar_One\<^sub>I_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_One\<^sub>E TYPE('s len_intvl) TYPE('c) TYPE('c) TYPE('a) TYPE('a list)
                     F whatever T T \<lbrakk>x:1\<rwpar> (\<lambda>l. length l = 1) hd (\<lambda>_. True) True True\<close>
  unfolding Guess_Scalar_One\<^sub>E_def ..

(* lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_One\<^sub>I TYPE('i set) TYPE('c::sep_algebra) TYPE('a) TYPE('i \<Rightarrow> 'a)
                     F (\<lambda>s T x. \<big_ast> (A s T x) s) T {any} (\<lambda>_. True) (\<lambda>x _. x) \<close>
  unfolding Guess_Scalar_One\<^sub>I_def .. *)

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_One\<^sub>I TYPE('i set) TYPE('c) TYPE('c::sep_algebra) TYPE('a) TYPE('i \<Rightarrow> 'a)
                     F (\<lambda>s x. \<big_ast> (A s x) s) T T {i} (\<lambda>_. True) (\<lambda>x _. x) (\<lambda>_. True) True True\<close>
  unfolding Guess_Scalar_One\<^sub>I_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_One\<^sub>E TYPE('i set) TYPE('c) TYPE('c::sep_algebra) TYPE('a) TYPE('i \<Rightarrow> 'a)
                     F (\<lambda>s x. \<big_ast> (A s x) s) T T {i} (\<lambda>_. True) (\<lambda>f. f i) (\<lambda>_. True) True True\<close>
  unfolding Guess_Scalar_One\<^sub>E_def ..


paragraph \<open>Guess_Scalar_Assoc\<close>

lemma [\<phi>reason %\<phi>TA_guesser_default[bottom]]:
  \<open>Guess_Scalar_Assoc\<^sub>I TYPE('s::times) TYPE('c) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc\<^sub>I_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_Assoc\<^sub>I TYPE(rat) TYPE('c::share) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T ((<) 0) ((<) 0) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc\<^sub>I_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default+1]:
  \<open>Guess_Scalar_Assoc\<^sub>I TYPE(rat) TYPE('c::share_one) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T ((\<le>) 0) ((\<le>) 0) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc\<^sub>I_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default[bottom]]:
  \<open>Guess_Scalar_Assoc\<^sub>E TYPE('s::times) TYPE('c) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc\<^sub>E_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Scalar_Assoc\<^sub>E TYPE(rat) TYPE('c::share) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T ((<) 0) ((<) 0) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc\<^sub>E_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default+1]:
  \<open>Guess_Scalar_Assoc\<^sub>E TYPE(rat) TYPE('c::share_one) TYPE('c) TYPE('a) TYPE('a)
                      F F F whatever T ((\<le>) 0) ((\<le>) 0) (\<lambda>_ _ _. True) (\<lambda>s t. t * s) (\<lambda>_ _ x. x) True True\<close>
  unfolding Guess_Scalar_Assoc\<^sub>E_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default for
        \<open>Guess_Scalar_Assoc\<^sub>I TYPE(_ set) TYPE(_) TYPE(_) TYPE(_) TYPE(_) _ _ _ (\<lambda>s T x. \<big_ast> (?A s T x) s) _
                            _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Scalar_Mul Fc Fs
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul Fc Ft
\<Longrightarrow> Guess_Scalar_Assoc\<^sub>I TYPE(('i \<times> 'j) set) TYPE('c::sep_algebra) TYPE('c) TYPE('a) TYPE('i \<times> 'j \<Rightarrow> 'a)
                      Fs Ft Fc (\<lambda>s T x. \<big_ast> (A s T x) s) T (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_ _ _. True)
                      (\<times>) (\<lambda>_ _. case_prod) True True \<close>
  unfolding Guess_Scalar_Assoc\<^sub>I_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default for
        \<open>Guess_Scalar_Assoc\<^sub>E TYPE(_ set) TYPE(_) TYPE(_) TYPE(_) TYPE(_) _ _ _ (\<lambda>s T x. \<big_ast> (?A s T x) s) _
                            _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Scalar_Mul Fc Fs
\<Longrightarrow> Type_Variant_of_the_Same_Scalar_Mul Fc Ft
\<Longrightarrow> Guess_Scalar_Assoc\<^sub>E TYPE(('i \<times> 'j) set) TYPE('c::sep_algebra) TYPE('c) TYPE('a) TYPE('i \<times> 'j \<Rightarrow> 'a)
                      Fs Ft Fc (\<lambda>s T x. \<big_ast> (A s T x) s) T finite finite (\<lambda>_ _ _. True)
                      (\<times>) (\<lambda>_ _. curry) True True \<close>
  unfolding Guess_Scalar_Assoc\<^sub>E_def ..


paragraph \<open>Guess_(Un)Zip_of_Semimodule\<close>

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Zip_of_Semimodule TYPE(rat) TYPE('c::sep_magma) TYPE('a)
                           F any
                           (\<lambda>x. 0 \<le> x) (\<lambda>_ _ (x,y). x = y) (\<lambda>_ _ (x,y). x)
                           True True \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Unzip_of_Semimodule TYPE(rat) TYPE('c::sep_magma) TYPE('a)
                             F any
                             (\<lambda>x. 0 \<le> x) (\<lambda>_ _ x. True) (\<lambda>_ _ x. (x,x))
                             True True \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Zip_of_Semimodule TYPE(nat lcro_intvl) TYPE('c::sep_magma) TYPE('a list)
                           F any (\<lambda>_. True)
                           (\<lambda>t s (x,y). LCRO_Interval.width_of s = length x \<and> LCRO_Interval.width_of t = length y)
                           (\<lambda>_ _ (x,y). x @ y)
                           True True\<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Unzip_of_Semimodule TYPE(nat lcro_intvl) TYPE('c::sep_magma) TYPE('a list)
                             F any (\<lambda>_. True)
                             (\<lambda>t s x. LCRO_Interval.width_of s + LCRO_Interval.width_of t = length x)
                             (\<lambda>t s x. (drop (LCRO_Interval.width_of s) x, take (LCRO_Interval.width_of s) x))
                             True True\<close>
  unfolding Guess_Unzip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Zip_of_Semimodule TYPE('s len_intvl) TYPE('c::sep_magma) TYPE('a list)
                           F any (\<lambda>_. True)
                           (\<lambda>t s (y,x). length x = len_intvl.len s \<and> length y = len_intvl.len t)
                           (\<lambda>_ _ (y,x). x @ y)
                           True True\<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Unzip_of_Semimodule TYPE('s len_intvl) TYPE('c::sep_magma) TYPE('a list)
                             F any (\<lambda>_. True)
                             (\<lambda>t s x. length x = len_intvl.len s + len_intvl.len t)
                             (\<lambda>t s x. (drop (len_intvl.len s) x, take (len_intvl.len s) x))
                             True True\<close>
  unfolding Guess_Unzip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Zip_of_Semimodule TYPE('i set) TYPE('c::sep_algebra) TYPE('i \<Rightarrow> 'a)
                           F (\<lambda>s x. \<big_ast> (A s x) s)
                           (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ D\<^sub>g (f,g). f \<oplus>\<^sub>f[D\<^sub>g] g) True True \<close>
  unfolding Guess_Zip_of_Semimodule_def ..

lemma [\<phi>reason %\<phi>TA_guesser_default]:
  \<open>Guess_Unzip_of_Semimodule TYPE('i set) TYPE('c::sep_algebra) TYPE('i \<Rightarrow> 'a)
                             F (\<lambda>s x. \<big_ast> (A s x) s)
                             (\<lambda>_. True) (\<lambda>_ _ _. True) (\<lambda>_ _ f. (f,f)) True True \<close>
  unfolding Guess_Unzip_of_Semimodule_def ..


paragraph \<open>ML Library\<close>

ML_file \<open>library/phi_type_algebra/guess_semimodule.ML\<close>


subsubsection \<open>Semimodule Scalar Zero\<close>

context begin

private lemma \<phi>TA_M0_rule:
  \<open> (\<And>x. Ant \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> OPEN undefined (F zero)) True
                  @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_Zero F zero \<close>
  unfolding Semimodule_Zero_def Action_Tag_def Premise_def
            Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def OPEN_def
  by (clarsimp simp add: BI_eq_iff Transformation_def; blast)

private lemma \<phi>TA_M0c_rule:
  \<open> (\<And>x. Ant \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> MAKE undefined (F zero))
                  @action \<phi>TA_subgoal undefined)
\<Longrightarrow> Semimodule_Zero F zero
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Closed_Semimodule_Zero F zero \<close>
  unfolding Semimodule_Zero_def Action_Tag_def Premise_def Identity_Element\<^sub>I_def Identity_Element\<^sub>E_def
            Closed_Semimodule_Zero_def MAKE_def
  by (clarsimp simp add: BI_eq_iff Transformation_def; blast)

private lemma \<phi>TA_M0_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> OPEN undefined T) True @action \<phi>TA_subgoal A)
 \<equiv> (Ant \<Longrightarrow> Identity_Element\<^sub>I (x \<Ztypecolon> T) True ) \<close>
  unfolding Action_Tag_def atomize_imp OPEN_def .

private lemma \<phi>TA_M0c_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> MAKE undefined T) @action \<phi>TA_subgoal A)
 \<equiv> (Ant \<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> T) ) \<close>
  unfolding Action_Tag_def atomize_imp MAKE_def .

ML_file \<open>library/phi_type_algebra/semimodule_zero.ML\<close>

end

\<phi>property_deriver Semimodule_Zero 129 for (\<open>Semimodule_Zero _ _\<close>)
    = \<open>Phi_Type_Derivers.semimodule_zero\<close>

\<phi>property_deriver Closed_Semimodule_Zero 130
  for (\<open>Closed_Semimodule_Zero _ _\<close>)
  requires Semimodule_Zero
    = \<open>Phi_Type_Derivers.closed_semimodule_zero\<close>


subsubsection \<open>Semimodule Scalar Identity\<close>

context begin

private lemma \<phi>TA_MI\<^sub>E_rule:
  \<open> (\<And>x. Ant
      \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
      \<longrightarrow> (x \<Ztypecolon> F one \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> T\<^sub>1 \<w>\<i>\<t>\<h> P\<^sub>E x) @action \<phi>TA_subgoal NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_One\<^sub>E F T\<^sub>1 one D f P\<^sub>E \<close>
  unfolding Semimodule_One\<^sub>E_def Action_Tag_def Premise_def Transformation_def
  by (clarsimp; metis)

private lemma \<phi>TA_MI\<^sub>I_rule:
  \<open> (\<And>x. Ant
      \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> D x
      \<longrightarrow> (x \<Ztypecolon> T\<^sub>1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x \<Ztypecolon> F one \<w>\<i>\<t>\<h> P\<^sub>I x) @action \<phi>TA_subgoal NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_One\<^sub>I F T\<^sub>1 one D f P\<^sub>I \<close>
  unfolding Semimodule_One\<^sub>I_def Action_Tag_def Premise_def Transformation_def
  by (clarsimp; metis)

ML_file \<open>library/phi_type_algebra/semimodule_identity.ML\<close>

end

\<phi>property_deriver Semimodule_One\<^sub>I 130 for (\<open>Semimodule_One\<^sub>I _ _ _ _ _ _\<close>)
    = \<open>Phi_Type_Derivers.semimodule_identity_I\<close>

\<phi>property_deriver Semimodule_One\<^sub>E 130 for (\<open>Semimodule_One\<^sub>E _ _ _ _ _ _\<close>)
    = \<open>Phi_Type_Derivers.semimodule_identity_E\<close>

\<phi>property_deriver Semimodule_One 131
  requires Semimodule_One\<^sub>I and Semimodule_One\<^sub>E


subsubsection \<open>Semimodule Scalar Associative\<close>

text \<open>\<phi>-type embedding of separation quantifier \<open>x \<Ztypecolon> \<big_ast>[i\<in>I] T\<close> is a recursive example of this.

  The induction of the \<phi>-type should expand the scalar as the scalar usually represents the domain of the \<phi>-type abstraction. 
\<close>

context begin

private lemma \<phi>TA_MS\<^sub>I_rule:
  \<open> (\<And>t s x r y. Ant
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> Dx s t x \<and> r = smul s t \<and> f s t x = y
         \<longrightarrow> (x \<Ztypecolon> OPEN undefined (Fs s (OPEN undefined (Ft t T)))
             \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined (Fc r T)) @action \<phi>TA_subgoal NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>I Fs Ft Fc T Ds Dt Dx smul f \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>I_def Action_Tag_def Premise_def MAKE_def OPEN_def
  by clarsimp

private lemma \<phi>TA_MS\<^sub>E_rule:
  \<open> (\<And>t s r x. Ant
         \<longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Ds s \<and> Dt t \<and> r = smul s t \<and> Dx s t x
         \<longrightarrow> (x \<Ztypecolon> OPEN undefined (Fc r T)
             \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f s t x \<Ztypecolon> MAKE undefined (Fs s (MAKE undefined (Ft t T))))
         @action \<phi>TA_subgoal NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_Scalar_Assoc\<^sub>E Fs Ft Fc T Ds Dt Dx smul f \<close>
  unfolding Semimodule_Scalar_Assoc\<^sub>E_def Action_Tag_def Premise_def MAKE_def OPEN_def
  by clarsimp

private lemma \<phi>TA_MS\<^sub>I_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> C \<longrightarrow> (x \<Ztypecolon> OPEN undefined U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined T \<w>\<i>\<t>\<h> P) @action A)
 \<equiv> (Ant \<Longrightarrow> C \<Longrightarrow> x \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>TA_IND_TARGET T \<w>\<i>\<t>\<h> P) \<close>
  unfolding Action_Tag_def atomize_imp \<phi>TA_IND_TARGET_def OPEN_def MAKE_def .


ML_file \<open>library/phi_type_algebra/semimodule_scalar.ML\<close>
                            
end

\<phi>property_deriver Semimodule_Scalar_Assoc\<^sub>I 130 for (\<open>Semimodule_Scalar_Assoc\<^sub>I _ _ _ _ _ _ _ _ _\<close>)
    = \<open>Phi_Type_Derivers.semimodule_assoc_I\<close>

\<phi>property_deriver Semimodule_Scalar_Assoc\<^sub>E 130 for (\<open>Semimodule_Scalar_Assoc\<^sub>E _ _ _ _ _ _ _ _ _\<close>)
    = \<open>Phi_Type_Derivers.semimodule_assoc_E\<close>

\<phi>property_deriver Semimodule_Scalar_Assoc 131
  requires Semimodule_Scalar_Assoc\<^sub>I and Semimodule_Scalar_Assoc\<^sub>E

\<phi>property_deriver Semimodule_NonDistr_no0 132
  requires Semimodule_Scalar_Assoc and Semimodule_One
       and Semimodule_No_SDistr

\<phi>property_deriver Semimodule_NonDistr 133
  requires Semimodule_NonDistr_no0 and Semimodule_Zero


subsubsection \<open>Semimodule Scalar Distributivity - Zip\<close>

context begin

bundle \<phi>TA_MD =
  [[\<phi>reason_default_pattern \<open>equation\<^sub>2\<^sub>1 ?c ?a ?b\<close> \<Rightarrow> \<open>equation\<^sub>2\<^sub>1 _ _ _\<close> (1000)]]

\<phi>reasoner_group \<A>_partial_add_local = (3850, [3850, 3850]) in \<A>_partial_add__top \<open>\<close>

private lemma \<phi>TA_MD\<^sub>Z_rule:
  \<open> (\<And>s t x r z. Ant
         \<Longrightarrow> equation\<^sub>2\<^sub>1 s t r
         \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> Dx t s x \<and> zi t s x = z
         \<Longrightarrow> (x \<Ztypecolon> NO_SIMP \<phi>Prod (OPEN undefined (F t)) (OPEN undefined (F s))
             \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> z \<Ztypecolon> MAKE undefined (F r))
         @action \<phi>TA_subgoal NToA)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx zi \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def Action_Tag_def Premise_def Transformation_def
            OPEN_def MAKE_def NO_SIMP_def equation\<^sub>2\<^sub>1_def
  by clarsimp

private lemma \<phi>TA_MD\<^sub>U_rule:
  \<open> (\<And>s t r x. Ant
         \<Longrightarrow> equation\<^sub>2\<^sub>1 s t r
         \<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Ds s \<and> Ds t \<and> Dx t s x
         \<Longrightarrow> (x \<Ztypecolon> OPEN undefined (F r)
             \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> uz t s x \<Ztypecolon> NO_SIMP \<phi>Prod (MAKE undefined (F t)) (MAKE undefined (F s)))
        @action \<phi>TA_subgoal (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> F r \<Rightarrow> \<s>\<p>\<l>\<i>\<t>-\<s>\<c>\<a>\<l>\<a>\<r> s t)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_def Action_Tag_def Premise_def Transformation_def
            OPEN_def MAKE_def NO_SIMP_def equation\<^sub>2\<^sub>1_def
  by clarsimp

private lemma \<phi>TA_MD\<^sub>U_cong:
  \<open> Ds \<equiv> Ds'
\<Longrightarrow> (\<And>t s x. Ds' t \<Longrightarrow> Ds' s \<Longrightarrow> s ##\<^sub>+ t \<Longrightarrow> Dx t s x \<equiv> Dx' t s x)
\<Longrightarrow> (\<And>t s x. Ds' t \<Longrightarrow> Ds' s \<Longrightarrow> s ##\<^sub>+ t \<Longrightarrow> Dx' t s x \<Longrightarrow> uz t s x \<equiv> uz' t s x)
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>S F Ds Dx uz \<equiv> Semimodule_SDistr_Homo\<^sub>S F Ds' Dx' uz' \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>S_def atomize_eq Transformation_def
  by clarsimp metis

private lemma \<phi>TA_MD\<^sub>Z_cong:
  \<open> Ds \<equiv> Ds'
\<Longrightarrow> (\<And>t s x. Ds' t \<Longrightarrow> Ds' s \<Longrightarrow> s ##\<^sub>+ t \<Longrightarrow> Dx t s x \<equiv> Dx' t s x)
\<Longrightarrow> (\<And>t s x. Ds' t \<Longrightarrow> Ds' s \<Longrightarrow> s ##\<^sub>+ t \<Longrightarrow> Dx' t s x \<Longrightarrow> z t s x \<equiv> z' t s x)
\<Longrightarrow> Semimodule_SDistr_Homo\<^sub>Z F Ds Dx z \<equiv> Semimodule_SDistr_Homo\<^sub>Z F Ds' Dx' z' \<close>
  unfolding Semimodule_SDistr_Homo\<^sub>Z_def atomize_eq Transformation_def
  by (auto; metis)

private lemma \<phi>TA_MD\<^sub>Z_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> C2 \<longrightarrow> C \<longrightarrow> (x \<Ztypecolon> OPEN undefined U\<^sub>1 \<^emph> OPEN undefined U\<^sub>2
                             \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined T \<w>\<i>\<t>\<h> P) @action A)
 \<equiv> (Ant @action \<phi>TA_ANT \<Longrightarrow> C2 \<Longrightarrow> C \<Longrightarrow> x \<Ztypecolon> U\<^sub>1 \<^emph> U\<^sub>2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<phi>TA_IND_TARGET T \<w>\<i>\<t>\<h> P @action \<phi>TA_ToA_elim) \<close>
  unfolding Action_Tag_def atomize_imp \<phi>TA_IND_TARGET_def OPEN_def MAKE_def equation\<^sub>2\<^sub>1_def .

private lemma \<phi>TA_MD\<^sub>U_rewr_IH:
  \<open> Trueprop (Ant \<longrightarrow> C2 \<longrightarrow> C \<longrightarrow> (x \<Ztypecolon> OPEN undefined T
                             \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined U\<^sub>1 \<^emph> MAKE undefined U\<^sub>2 \<w>\<i>\<t>\<h> P) @action \<phi>TA_subgoal (to (\<t>\<r>\<a>\<v>\<e>\<r>\<s>\<e> \<p>\<a>\<t>\<t>\<e>\<r>\<n> AA \<Rightarrow> A)))
 \<equiv> (Ant @action \<phi>TA_ANT \<Longrightarrow> C2 \<Longrightarrow> C \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<^sub>1 \<^emph> U\<^sub>2 \<w>\<i>\<t>\<h> P @action (to A)) \<close>
  unfolding Action_Tag_def atomize_imp \<phi>TA_IND_TARGET_def OPEN_def MAKE_def .

private lemma \<phi>TA_MD\<^sub>Z_rewr_pre:
  \<open> (Ant \<Longrightarrow> C2 \<Longrightarrow> C \<Longrightarrow> x \<Ztypecolon> NO_SIMP \<phi>Prod T U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>)
  \<equiv> Trueprop (Ant \<longrightarrow> C2 \<longrightarrow> C \<longrightarrow> (x \<Ztypecolon> T \<^emph> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P) @action \<A>) \<close>
  unfolding atomize_imp Action_Tag_def NO_SIMP_def .

private lemma \<phi>TA_MD\<^sub>U_rewr_pre:
  \<open> (Ant \<Longrightarrow> C2 \<Longrightarrow> C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> NO_SIMP \<phi>Prod T U \<w>\<i>\<t>\<h> P @action \<A>)
  \<equiv> Trueprop (Ant \<longrightarrow> C2 \<longrightarrow> C \<longrightarrow> (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph> U \<w>\<i>\<t>\<h> P) @action \<A>) \<close>
  unfolding atomize_imp Action_Tag_def NO_SIMP_def .

ML_file \<open>library/phi_type_algebra/semimodule_distrib_zip.ML\<close>

end

\<phi>property_deriver Semimodule_SDistr_Homo\<^sub>Z 130 for (\<open>Semimodule_SDistr_Homo\<^sub>Z _ _ _ _\<close>)
    = \<open>Phi_Type_Derivers.semimodule_distrib_zip\<close>

\<phi>property_deriver Semimodule_SDistr_Homo\<^sub>S 130 for (\<open>Semimodule_SDistr_Homo\<^sub>S _ _ _ _\<close>)
    = \<open>Phi_Type_Derivers.semimodule_distrib_unzip\<close>

\<phi>property_deriver Semimodule_SDistr_Homo 131
  requires Semimodule_SDistr_Homo\<^sub>Z and Semimodule_SDistr_Homo\<^sub>S

\<phi>property_deriver Semimodule_NonAssoc 132
  requires Semimodule_SDistr_Homo and Semimodule_Zero
       and Semimodule_One

\<phi>property_deriver Semimodule_no0 133
  requires Semimodule_Scalar_Assoc and Semimodule_One
       and Semimodule_SDistr_Homo

\<phi>property_deriver Semimodule 134
  requires Semimodule_no0 and Semimodule_Zero

(*
declare Is_Invariant[where PC=\<open>Semimodule_SDistr_Homo\<^sub>Z\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]
        Is_Invariant[where PC=\<open>Semimodule_SDistr_Homo\<^sub>S\<close>, \<phi>reason default %\<phi>TA_guesser_assigning_variant]
*)


subsubsection \<open>Construct Abstraction from Concrete Representation (by Itself)\<close>

(*Designed only for primitives, so can be buggy for advanced and particularly recursive \<phi>-types*)

context begin

private lemma \<phi>TA_TrCstr_rule:
  \<open> Ant \<longrightarrow> (c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A) @action \<phi>TA_subgoal undefined
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> c \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<close>
  unfolding Action_Tag_def
  by simp

ML_file \<open>library/phi_type_algebra/constr_abst_weak.ML\<close>

end

\<phi>property_deriver Make_Abstraction_from_Raw 130
  for ( \<open>\<forall>x. Premise _ _ \<longrightarrow> (x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?f x \<Ztypecolon> ?T)\<close>
      | \<open>Premise _ _ \<longrightarrow> (?x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T)\<close>
      | \<open>\<forall>x. x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?f x \<Ztypecolon> ?T\<close>
      | \<open>?x \<Ztypecolon> Itself \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?y \<Ztypecolon> ?T\<close> )
  requires Warn_if_contains_Sat
    = \<open> Phi_Type_Derivers.Make_Abstraction_from_Raw \<close>



subsubsection \<open>Destruct Abstraction down to Concrete Representation (by Itself)\<close>

(*Designed only for primitives, so can be buggy for advanced and particularly recursive \<phi>-types*)

context begin

private lemma \<phi>TA_TrRA_rule:
  \<open> (\<And>x. Ant \<longrightarrow> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y) @action \<phi>TA_subgoal (to (Itself::('b,'b) \<phi>)))
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> \<forall>x. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y::'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @action to (Itself::('b,'b) \<phi>)) \<close>
  unfolding Action_Tag_def
  by simp

private lemma \<phi>TA_TrRA_simp:
  \<open> \<forall>x. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y::'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r x y @action to (Itself::('b,'b) \<phi>))
 \<Longrightarrow> Abstract_Domain T P
 \<Longrightarrow> (\<And>x y. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P x \<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> r' x y : r x y )
 \<Longrightarrow> \<forall>x. (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y::'b) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. r' x y @action to (Itself::('b,'b) \<phi>)) \<close>
  unfolding Transformation_def Action_Tag_def Inhabited_def Simplify_def
            Abstract_Domain_def Premise_def \<r>EIF_def
  by (clarsimp, smt (verit, del_insts))

ML_file \<open>library/phi_type_algebra/open_all_abstraction.ML\<close>

end

\<phi>property_deriver Open_Abstraction_to_Raw 130 for ( \<open>\<forall>x. (x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself)\<close>
                                                | \<open>\<forall>x. x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r x y @action to Itself\<close>
                                                | \<open>?x \<Ztypecolon> ?T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> Itself \<s>\<u>\<b>\<j> y. ?r' y @action to Itself\<close>)
  requires Warn_if_contains_Sat
    = \<open> Phi_Type_Derivers.open_all_abstraction \<close>

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
\<Longrightarrow> TERM (Identity_Elements\<^sub>I (F \<circle>))
\<Longrightarrow> Identity_Elements\<^sub>I (F \<circle>) D\<^sub>I P\<^sub>I @action \<A>_template_reason undefined
\<Longrightarrow> Identity_Elements\<^sub>E (F \<circle>) D\<^sub>E @action \<A>_template_reason undefined
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
    = \<open>fn quiet => K (Phi_Type_Derivers.SE_Trim_Empty quiet) \<close>

lemmas [\<phi>reason_template default 40 pass: \<open>(Phi_Type_Derivers.SE_Trim_Empty__generation_pass, K I)\<close>] =
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

lemma [\<phi>reason %guess_tyop_commute_default for \<open>Guess_Tyops_Commute _ _ ?var_F' _ _ _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Parameter_Variant_of_the_Same_Type F var_F'
\<Longrightarrow> Guess_Tyops_Commute Any F var_F' G G' uF uF' uG uG' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute Any F var_F' G G' uF uF' uG uG' T D r ants conds \<close> .

lemma [\<phi>reason %guess_tyop_commute_default for \<open>Guess_Tyops_Commute _ _ _ _ ?var_G' _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Parameter_Variant_of_the_Same_Type G var_G'
\<Longrightarrow> Guess_Tyops_Commute Any F F' G var_G' uF uF' uG uG' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute Any F F' G var_G' uF uF' uG uG' T D r ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init except \<open>Guess_Tyops_Commute True _ _ _ ?var_F' _ _ _ _ _ _ _ _ _\<close>
                                         \<open>Guess_Tyops_Commute True _ ?var_G' _ _ _ _ _ _ _ _ _ _ _\<close>]:
  \<open> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G T x) : (x \<Ztypecolon> G T) )
\<Longrightarrow> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G' T x) : (x \<Ztypecolon> G' T) )
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' var_unfolded_G var_unfolded_G' uF uF' T D r ants conds
\<Longrightarrow> Guess_Tyops_Commute True G G' F F' var_unfolded_G var_unfolded_G' uF uF' T D r ants conds\<close> .

lemma [\<phi>reason %\<phi>TA_guesser_init except \<open>Guess_Tyops_Commute False _ _ _ ?var_G' _ _ _ _ _ _ _ _ _\<close>
                                        \<open>Guess_Tyops_Commute False _ ?var_F' _ _ _ _ _ _ _ _ _ _ _\<close>]:
  \<open> (\<And>T x. \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[\<phi>deriver_expansion] (var_unfolded_G T x) : (x \<Ztypecolon> G T) )
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
  \<open> Type_Variant_of_the_Same_Type_Operator F F' \<or>\<^sub>c\<^sub>u\<^sub>t True
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator G G' \<or>\<^sub>c\<^sub>u\<^sub>t True
\<Longrightarrow> Guess_Tyops_Commute both F F' G G' uF uF' any any' T (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True\<close>
  unfolding Guess_Tyops_Commute_def ..

lemma [\<phi>reason %guess_tyop_commute_fallback for \<open>Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Type_Operator2 F F' \<or>\<^sub>c\<^sub>u\<^sub>t True
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator G G'\<^sub>T \<or>\<^sub>c\<^sub>u\<^sub>t True
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator G G'\<^sub>U \<or>\<^sub>c\<^sub>u\<^sub>t True
\<Longrightarrow> Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 both G G'\<^sub>T G'\<^sub>U F F' uG uG'\<^sub>T uG'\<^sub>U uF uF' T U
                          (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) True True \<close>
  unfolding Guess_Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def ..

lemma [\<phi>reason %guess_tyop_commute_fallback for \<open>Guess_Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _\<close>]:
  \<open> Type_Variant_of_the_Same_Type_Operator2 G G' \<or>\<^sub>c\<^sub>u\<^sub>t True
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F F'\<^sub>T \<or>\<^sub>c\<^sub>u\<^sub>t True
\<Longrightarrow> Type_Variant_of_the_Same_Type_Operator F F'\<^sub>U \<or>\<^sub>c\<^sub>u\<^sub>t True
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


subparagraph \<open>Deriving Bubbling ToA\<close>



(*
subparagraph \<open>Rules\<close>

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv (\<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T) eq\<close>
  unfolding Has_Bubbling_def .

lemma [\<phi>reason %object_equiv_cut]:
  \<open> Object_Equiv T eq
\<Longrightarrow> Object_Equiv (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T) eq\<close>
  unfolding Bubbling_def .

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>I T D P
\<Longrightarrow> Identity_Elements\<^sub>I (\<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T) D P \<close>
  unfolding Has_Bubbling_def .

lemma [\<phi>reason %identity_element_cut]:
  \<open> Identity_Elements\<^sub>E T D
\<Longrightarrow> Identity_Elements\<^sub>E (\<h>\<a>\<s>-\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> T) D \<close>
  unfolding Has_Bubbling_def .
*)

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
          (x \<Ztypecolon> OPEN undefined (G (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F T))
          \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' (MAKE undefined (G' T)) \<s>\<u>\<b>\<j> y. r x y)
        @action \<phi>TA_subgoal \<A>simp)
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
\<Longrightarrow> (\<And>x. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<longrightarrow>
           (x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (OPEN undefined (G T))
            \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined (G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F' T)) \<s>\<u>\<b>\<j> y. r x y)
        @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute F F' G G' T D r\<close>
  unfolding Action_Tag_def Tyops_Commute_def Premise_def embedded_func_def Bubbling_def OPEN_def MAKE_def
  by clarsimp
  

lemma \<phi>TA_TyComm\<^sub>1\<^sub>_\<^sub>2\<^sub>I_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'\<^sub>T
\<Longrightarrow> Parameter_Variant_of_the_Same_Type F F'\<^sub>U
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<longrightarrow>
          (x \<Ztypecolon> OPEN undefined (G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U))
           \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F (MAKE undefined (G T U)) \<s>\<u>\<b>\<j> y. r x y)
        @action \<phi>TA_subgoal \<A>simp)
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
\<Longrightarrow> (\<And>x. Ant \<longrightarrow>
       \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<longrightarrow>
        (x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F (OPEN undefined (G T U))
         \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined (G' (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>T T) (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F'\<^sub>U U)) \<s>\<u>\<b>\<j> y. r x y)
                      \<comment>\<open>^ target of inductive expansion. The same limitation as above.\<close>
       @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 F F'\<^sub>T F'\<^sub>U G G' T U D r\<close>
  unfolding Action_Tag_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def embedded_func_def OPEN_def MAKE_def Bubbling_def
  by clarsimp

lemma \<phi>TA_TyComm\<^sub>2\<^sub>_\<^sub>1\<^sub>I_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x. Ant \<longrightarrow>
          \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<longrightarrow>
          (x \<Ztypecolon> OPEN undefined (G (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F T U))
            \<comment>\<open>^ target of inductive expansion, needs \<open>to (\<c>\<o>\<m>\<m>\<u>\<t>\<e> G F)\<close>\<close>
           \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> F' (MAKE undefined (G'\<^sub>T T)) (MAKE undefined (G'\<^sub>U U)) \<s>\<u>\<b>\<j> y. r x y)
        @action \<phi>TA_subgoal \<A>simp)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 G G'\<^sub>T G'\<^sub>U F F' T U D r\<close>
  unfolding Action_Tag_def Tyops_Commute\<^sub>1\<^sub>_\<^sub>2_def Premise_def Bubbling_def OPEN_def MAKE_def
  by clarsimp

lemma \<phi>TA_TyComm\<^sub>2\<^sub>_\<^sub>1\<^sub>E_gen:
  \<open> Parameter_Variant_of_the_Same_Type F F'
\<Longrightarrow> \<r>Success \<comment>\<open>Success of generating deriving rule\<close>
\<Longrightarrow> (\<And>x. Ant \<longrightarrow>
       \<p>\<r>\<e>\<m>\<i>\<s>\<e> D x \<longrightarrow>
        (x \<Ztypecolon> \<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F' (OPEN undefined (G'\<^sub>T T)) (OPEN undefined (G'\<^sub>U U))
         \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> MAKE undefined (G (\<b>\<u>\<b>\<b>\<l>\<i>\<n>\<g> F T U)) \<s>\<u>\<b>\<j> y. r x y)
                     \<comment>\<open>^ target of inductive expansion. The same limitation as above.\<close>
       @action \<phi>TA_subgoal undefined)
\<Longrightarrow> \<r>Success
\<Longrightarrow> \<o>\<b>\<l>\<i>\<g>\<a>\<t>\<i>\<o>\<n> True
\<Longrightarrow> Ant @action \<phi>TA_ANT
\<Longrightarrow> Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 G G'\<^sub>T G'\<^sub>U F F' T U D r\<close>
  unfolding Action_Tag_def Tyops_Commute\<^sub>2\<^sub>_\<^sub>1_def Premise_def embedded_func_def OPEN_def MAKE_def Bubbling_def
  by clarsimp

(*TODO: bi-commutativity!*)

ML_file \<open>library/phi_type_algebra/gen_tyops_commute.ML\<close>

\<phi>property_deriver Commutativity_Deriver\<^sub>I 200
    = \<open>fn quiet => K (Phi_Type_Derivers.meta_Tyops_Commute (false, 1) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver\<^sub>E 200
    = \<open>fn quiet => K (Phi_Type_Derivers.meta_Tyops_Commute (false, 2) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver 200
    = \<open>fn quiet => K (Phi_Type_Derivers.meta_Tyops_Commute (false, 3) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver\<^sub>I_rev 200
    = \<open>fn quiet => K (Phi_Type_Derivers.meta_Tyops_Commute (true, 2) quiet) \<close>
  \<comment> \<open>The name is reversed, i.e., I for E, E for I, but the deriving process is unchanged.\<close>

\<phi>property_deriver Commutativity_Deriver\<^sub>E_rev 200
    = \<open>fn quiet => K (Phi_Type_Derivers.meta_Tyops_Commute (true, 1) quiet) \<close>

\<phi>property_deriver Commutativity_Deriver_rev 200
    = \<open>fn quiet => K (Phi_Type_Derivers.meta_Tyops_Commute (true, 3) quiet) \<close>



section \<open>Deriving Configures for Specific Abstract Algebras\<close>

subsubsection \<open>Common\<close>

lemmas [\<phi>constraint_expansion global] =
  Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral Nat.nat.inject

lemmas [\<phi>constraint_expansion] =
  Basic_BNFs.prod_set_defs


subsubsection \<open>List\<close>

declare list.rel_eq[iff]

definition \<open>zip' = case_prod zip\<close>
definition \<open>unzip' l = (map fst l, map snd l)\<close>

lemma case_unzip'[simp]:
  \<open>(case unzip' x of (a,b) \<Rightarrow> f a b) = (let a = map fst x; b = map snd x in f a b)\<close>
  unfolding unzip'_def
  by simp

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

lemma list_all2_reduct_rel[simp]:
  \<open>list_all2 (\<lambda>a b. b = f a \<and> P a) = (\<lambda>a' b'. b' = map f a' \<and> list_all P a')\<close>
  apply (clarsimp simp add: fun_eq_iff)
  subgoal for x y by (induct x arbitrary: y; simp; case_tac y; simp; blast) .

lemmas [\<phi>constraint_expansion] =
  list.size map_eq_Cons_conv list_all2_lengthD[THEN HOL.Eq_TrueI]

paragraph \<open>Separatable Mappers\<close>

lemma [\<phi>reason add]:
  \<open>compositional_mapper map map map UNIV f g\<close>
  unfolding compositional_mapper_def
  by clarsimp

lemma [\<phi>reason add]:
  \<open>separatable_unzip zip' unzip' UNIV map map map f g\<close>
  unfolding separatable_unzip_def unzip'_def zip'_def
  by (clarsimp simp add: zip_eq_conv)

lemma [\<phi>reason add]:
  \<open>separatable_zip unzip' zip' {(la,lb). length la = length lb} map map map f g\<close>
  unfolding separatable_zip_def unzip'_def zip'_def
  by (clarsimp simp add: zip_eq_conv, metis map_fst_zip map_map map_snd_zip)

lemma [\<phi>reason add]:
  \<open>domain_by_mapper set map set f UNIV\<close>
  unfolding domain_by_mapper_def
  by clarsimp

lemma [\<phi>reason add]:
  \<open>domain_of_inner_map map set\<close>
  unfolding domain_of_inner_map_def
  by clarsimp


subsubsection \<open>Sum\<close>

lemma pred_sum_eq_case_sum[\<phi>constraint_expansion]:
  \<open>pred_sum P Q x \<longleftrightarrow> case_sum P Q x\<close>
  by (cases x; simp)

lemma collapse_case_sum[simp]:
  \<open>(case x of Inl x \<Rightarrow> Inl x | Inr x \<Rightarrow> Inr x) = x\<close>
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

lemma rel_fun__const_True[simp]:
  \<open>rel_fun (=) (\<lambda>x y. True) = (\<lambda>x y. True)\<close>
  by (simp add: fun_eq_iff rel_fun_def)

subsubsection \<open>Production\<close>

lemma [\<phi>constraint_expansion, simp]:
  \<open>pred_prod (\<lambda>a. True) P x \<longleftrightarrow> P (snd x)\<close>
  \<open>pred_prod Q (\<lambda>a. True) x \<longleftrightarrow> Q (fst x)\<close>
  by (cases x; simp)+

declare Lifting.pred_prod_beta[\<phi>deriver_simp]

section \<open>Clean-up\<close>

hide_const (open) introduced

end
