(* AUTHOR: Qiyuan Xu, 2022 *)

theory VDT_Example
  imports "Virtual_Datatype.Virtual_Datatype" "Phi_Document.Base"
begin

section \<open>Introduction\<close>

text \<open>Virtual Datatype (VDT) provides a locale approach for inheritance of datatypes
  and any proof elements including theorems, definitions, and notations about these datatypes.
  In essence, it is a locale that constrains and assumes partially some constructors of
  a concrete type parameter, and the inheritance is merging the assumptions, i.e., combination
  of locales.
  As a set of assumptions and constraints, it is not a concrete type but more like an abstract
  interface.
  Theories and proofs above it are therefore abstract and available for any concrete types
  that match the interface, via interpreting the locale by @{command interpretation}.

Recursive datatype is supported.
For each constructor, a corresponding destructor is provided.
Case-split is not supported right now but is planned, for case-splitting only assumed constructors
and leaving future constructors in underscore, e.g. \<open>case x of Known_Constructor v \<Rightarrow> f v | _ \<Rightarrow>
the_case_for_future_constructors.\<close>

A typical usage of the virtual datatype is formalizing program semantics partially and modularly.
For example, it is suitable to model the deep representation of program values.
A minimal common set of the semantics can be provided, including maybe only integer values.
Then for a language having enumeration values, corresponding formalization can extend the previous
virtual datatype of integers.

Virtual datatype is implemented by locales.
Actually, it is the dual of the Statespace by Norbert Schirmer~\cite{Statespace}.
Maintained by locales, a Statespace is essentially a function \<open>Name \<Rightarrow> Value\<close> from a set of
distinct \<open>Names\<close> to a deep embedding of \<open>Values\<close>.
By contrast, Virtual Datatype is a production \<open>Constructor \<times> Value\<close> where the \<open>Value\<close> is
still the deep embedding of that \<open>Value\<close> in Statespace, and \<open>Constructor\<close> is the counterpart of
the \<open>Name\<close> in Statespace. Indeed, the \<open>Constructor\<close> and the \<open>Name\<close> are only different in
how we name them. \<close>


section \<open>Syntax\<close>

text \<open>
A virtual datatype is declared by command @{command virtual_datatype}.

  \begin{matharray}{rcl}
    @{command_def virtual_datatype} & : & \<open>theory \<rightarrow> theory\<close>\\
  \end{matharray}

  \<^rail>\<open>
    @@{command virtual_datatype} @{syntax environ}? @{syntax vdt_name} ('=' @{syntax vdt_descr})?
    ;
    @{syntax_def environ}: '(' 'in' @{syntax name} ')'
    ;
    @{syntax_def vdt_name}: @{syntax tyargs}? @{syntax name} ('::' @{syntax sort})?
    ;
    @{syntax_def tyargs}: (@{syntax typefree} | '(' (@{syntax typefree} + @{syntax typefree}) ')')
    ;
    @{syntax_def vdt_descr}: (@{syntax parents} | @{syntax constructors} | @{syntax parents} '+' @{syntax constructors})
    ;
    @{syntax_def constructors}: (@{syntax name} '::' @{syntax type} + @{syntax constructors})
    ;
    @{syntax_def parents}: (@{syntax parent} + @{syntax parent})
    ;
    @{syntax_def parent}: (@{syntax qualifier} ':')? (@{syntax tyinsts})?
          @{syntax name} (@{syntax renames})?
    ;
    @{syntax_def tyinsts}: (@{syntax type} | '(' (@{syntax type} + @{syntax type}) ')')
    ;
    @{syntax_def renames}: '[' ((@{syntax name} '=' @{syntax name}) + @{syntax renames}) ']'
  \<close>

\<^descr> Optional @{syntax environ} indicates the locale of virtual datatype to extend the @{syntax environ}
  locale. Constructors of the virtual datatype are able to use types fixed or defined in the
  @{syntax environ}.
  If not given, no @{syntax environ} locale is used.

\<^descr> @{syntax vdt_name} indicates the name of the VDT,
  together with type arguments and the sort of the VDT.
  @{syntax tyargs} is a sequence of type variables parameterize the VDT, which resembles that in
  @{command datatype}.
  The actual sort of the VDT is the meet (intersection) of the given sort and the sorts of all
  parents.

\<^descr> @{syntax vdt_descr} describes the parents and new constructors of the VDT.
  If it is not given, the command defines an empty VDT that contains no constructors.

  In @{syntax vdt_descr}, a special type variable \<^typ>\<open>'self\<close> denotes the type of the VDT itself,
  allowing to define recursive VDT. Examples are given in the next section.

\<^descr> @{syntax constructors} are a sequence of name-type pairs for each constructor.
  A constructor should has exactly one argument.
  Multiple arguments can be aggregated into a tuple.
  None argument can be a unit.

\<^descr> @{syntax parents} give the parent VDTs to be inherit.
  The syntax resembles locale expression as in \cite{Isar}.
  @{syntax qualifier} is exactly that in locale expression, cf. \cite{Isar}.
  @{syntax tyinsts} are optional type instantiations for type parameters of the parent.
  @{syntax renames} can optionally rename constructors in the parent.
  \<^verbatim>\<open>[A=A',B=B']\<close> renames constructors \<^verbatim>\<open>A,B\<close> in the parent to \<^verbatim>\<open>A',B'\<close> in the child VDT.
  By this, it enables to inherit the same parent twice with different names of constructors.
\<close>

text \<open>\<^emph>\<open>Remark\<close>: different with inheriting a parent, it is unfeasible to rename constructors in
  a \<open>environ\<close> locale. A \<open>environ\<close> locale is opened using @{command context} during the parse
  phase.\<close>

section \<open>Usage through Examples\<close>

subsection \<open>Declare a VDT\<close>

text \<open>The following example defines a VDT named \<open>T1\<close> in sort \<open>plus\<close>, having two constructors
  \<open>C1\<close> and \<open>C2\<close> for \<^typ>\<open>nat\<close> and \<^typ>\<open>bool\<close> respectively.\<close>

virtual_datatype T1 :: plus =
  C1 :: nat
  C2 :: bool

text \<open>The essence of a VDT is a locale.\<close>

print_locale T1

locale T1_demo =
  fixes CONS_OF :: "'rep::plus \<Rightarrow> 'CONS_NAME"
    and C1 :: "('CONS_NAME, 'rep, nat)  Virtual_Datatype.Field"
    and C2 :: "('CONS_NAME, 'rep, bool) Virtual_Datatype.Field"
  assumes "Field.project C1 (Field.inject C1 n) = n"
    and   "Field.project C2 (Field.inject C2 b) = b"
    and  \<open>Field.name C1 \<noteq> Field.name C2\<close>

datatype ('CONS_NAME,'rep,'T) Field_demo =
  Field_demo (name: 'CONS_NAME) (project: "'rep \<Rightarrow> 'T") (inject: "'T \<Rightarrow> 'rep")

text \<open>\<^typ>\<open>'CONS_NAME\<close> can be any type that identifies constructors, e.g. \<^typ>\<open>string\<close> or \<^typ>\<open>nat\<close>.
\<^typ>\<open>'rep\<close> is the representation type of instances in the VDT.
A constructor of argument type \<open>'T\<close> is an injector from \<open>'T\<close> to \<open>'rep\<close> and reversely
a destructor is a projector from \<open>'rep\<close> to \<open>'T\<close>.
Type \<open>Field\<close> describes a constructor-destructor pair, together with the name of the constructor.
\<^term>\<open>CONS_OF\<close> gives the constructor of a given instance.

Assumptions constrain the injectors are injective and the projectors are their inverse functions.
The last assumption constrains the names of constructors are distinct.
\<close>


subsection \<open>Operations in VDT\<close>

text \<open>Operations are available inside the locale \<open>T1\<close> of the VDT.\<close>

context T1 begin

subsubsection \<open>Representation Type\<close>

text \<open>\<^typ>\<open>'rep\<close> is a sort plus!\<close>
typ \<open>'rep :: plus\<close>

subsubsection \<open>Constructor\<close>

term \<open>C1.mk 42 :: 'rep\<close> \<comment> \<open>Make an instance by constructor \<^term>\<open>C1\<close>\<close>

lemma \<open>C1.mk = Virtual_Datatype.Field.inject C1\<close>
  \<comment> \<open>\<open>C1.mk\<close> is merely a syntax sugar of \<open>Virtual_Datatype.Field.inject C1\<close>\<close>
  by simp

ML \<open>@{term C1.mk} = @{term \<open>Virtual_Datatype.Field.inject C1\<close>}\<close> \<comment> \<open>is True!\<close>

subsubsection \<open>Destructor\<close>

term \<open>C1.dest :: 'rep \<Rightarrow> nat\<close> \<comment> \<open>Destructor corresponding to \<^term>\<open>C1\<close>\<close>

lemma \<open>C1.dest = Virtual_Datatype.Field.project C1\<close>
  \<comment> \<open>Yet another syntax sugar\<close>
  by simp

lemma \<open>C1.dest (C1.mk x) = x\<close>
  \<comment> \<open>Automation for destruction is prepared.\<close>
  by simp

subsubsection \<open>Constructor Name\<close>

term \<open>C1.name :: 'CONS_NAME\<close> \<comment> \<open>The name of the constructor \<open>C1\<close>\<close>

lemma \<open>C1.name = Virtual_Datatype.Field.name C1\<close>
  \<comment> \<open>Yet another syntax sugar\<close>
  by simp

lemma "C1.name \<noteq> C2.name"
  \<comment> \<open>Names are distinct.\<close>
  by simp

subsubsection \<open>Equality\<close>

lemma "C1.mk x \<noteq> C2.mk y"
  \<comment> \<open>Representations under different constructor are different\<close>
  by simp

lemma "C1.mk x = C1.mk y \<longleftrightarrow> x = y"
  \<comment> \<open>Representations under the same constructor are injective w.r.t the constructor.\<close>
  by simp

subsubsection \<open>Misc\<close>

lemma "CONS_OF (C1.mk x) = C1.name"
  \<comment> \<open>You can use \<open>CONS_OF\<close> to get the constructor from a representation.\<close>
  by simp

lemma \<open>C1.is_instance (C1.mk x)\<close>
      \<open>\<not> C2.is_instance (C1.mk x)\<close>
      \<open>C1.is_instance v \<longleftrightarrow> (\<exists>x. v = C1.mk x)\<close>
  \<comment> \<open>\<open>C.is_instance\<close> asserts whether a representation is an instance of the constructor.\<close>
  unfolding C1.is_instance_def by simp+ 
end


subsection \<open>Inheritance\<close>

text \<open>It is feasible to declare a new VDT inheriting the previous VDTs.\<close>

virtual_datatype T2 = T1 +
  C3 :: int

text \<open>The locale of @{locale T2} extends all locales of its parents.\<close>

print_locale T2

locale T2_demo =
  fixes CONS_OF :: "'rep::plus \<Rightarrow> 'CONS_NAME"
    and C1 :: "('CONS_NAME, 'rep, nat)  Virtual_Datatype.Field"
    and C2 :: "('CONS_NAME, 'rep, bool) Virtual_Datatype.Field"
    and C3 :: "('CONS_NAME, 'rep, int) Virtual_Datatype.Field"
  assumes "Field.project C1 (Field.inject C1 n) = n"
    and   "Field.project C2 (Field.inject C2 b) = b"
    and   "Field.project C3 (Field.inject C3 i) = i"
    and \<open>distinct [Field.name C1, Field.name C2, Field.name C3]\<close>

text \<open>Proof elements defined on the parent VDT locales, are feasible on the children VDTs.\<close>

definition (in T1) "trn vx = C1.mk (if C2.dest vx then 1 else 0)"

lemma (in T1) trn: \<open>trn (C2.mk True) = C1.mk 1\<close>
  unfolding trn_def by simp

context T2 begin
thm trn  \<comment>  \<open>\<open>trn (C2.mk True) = C1.mk 1\<close>\<close>
end

text \<open>A parent may be inherited by multiple times in a child and
constructors in the parent are able to be renamed.

As an example, this \<open>T3\<close> inherits \<open>T1\<close> twice, by qualifying the second inheritance with name \<open>t1'\<close>
and renaming only the constructor \<open>C1\<close>.\<close>

virtual_datatype T3 = T1 + t1': T1[C1=C1']

text \<open>The resulting locale is like this. Note we only rename the \<open>C1\<close> so the constructor \<open>C2\<close>
is shared between two copies of \<open>T1\<close>.\<close>

print_locale T3

locale T3_demo =
  fixes CONS_OF :: "'rep::plus \<Rightarrow> 'CONS_NAME"
    and C1 :: "('CONS_NAME, 'rep, nat)  Virtual_Datatype.Field"
    and C2 :: "('CONS_NAME, 'rep, bool) Virtual_Datatype.Field"
    and C1' :: "('CONS_NAME, 'rep, nat) Virtual_Datatype.Field"
  assumes "Field.project C1 (Field.inject C1 n) = n"
    and   "Field.project C2 (Field.inject C2 b) = b"
    and   "Field.project C1' (Field.inject C1' n) = n"
    and \<open>distinct [Field.name C1, Field.name C2, Field.name C1']\<close>

text \<open>Proof elements of \<open>T1\<close> represent also two copies in \<open>T3\<close>\<close>

context T3 begin
thm trn     \<comment> \<open>@{thm trn}\<close>
thm t1'.trn \<comment> \<open>@{thm t1'.trn}\<close>
end

text \<open>Note there are two theorems \<open>trn\<close>, two constant \<open>trn\<close> and \<open>t1'.trn\<close>.
Two theorems share the same constructor \<open>C2\<close> but use their own different \<open>C1\<close> and \<open>C1'\<close>.\<close>


subsection \<open>Recursion\<close>

text \<open>Recursion is feasible by using \<^typ>\<open>'self\<close>.
For example, the following implements a list using VDT.\<close>

virtual_datatype TR =
  R_NIL :: "unit"
  R_CONS :: "nat \<times> 'self"

text \<open>A limitation is, lacking of case-split and Bounded Natural Functor (BNF)~\cite{datatypes},
it is unfeasible to define recursive functions over VDTs right now.
It is not a theoretical limitation and is planned in future.\<close>

context TR begin

definition "sth = R_CONS.mk (3, R_CONS.mk (2, R_NIL.mk ()))"
  \<comment> \<open>Instead, we use some trivial things to demonstrate the basic recursion.\<close>

end

text \<open>Recall VDT is by locale-based approach. It is a set of assumptions which can be inconsistent.\<close>

virtual_datatype Inconsistent =
  Inconsit :: "'self \<Rightarrow> bool"

text \<open>Therefore, any conclusion proven on VDTs is valid only until the VDTs are interpreted.\<close>

subsection \<open>Interpretation of VDT locale\<close>

datatype cons_names = MY_R_NIL | MY_R_CONS

interpretation interp1: TR
  "(\<lambda>l. case l of [] \<Rightarrow> MY_R_NIL | _ \<Rightarrow> MY_R_CONS)"
  \<open>Virtual_Datatype.Field MY_R_NIL (\<lambda>_. ()) (\<lambda>_. [])\<close>
  \<open>Virtual_Datatype.Field MY_R_CONS (\<lambda>l. case l of (a#l') \<Rightarrow> (a,l')) (\<lambda>(a,l'). a#l')\<close>
  by unfold_locales (auto split: list.split unit.split)
  
thm interp1.sth_def[simplified] \<comment> \<open>@{thm interp1.sth_def[simplified]}\<close>



section \<open>Documentation of Inner Implementation for Developers\<close>

text \<open>The essence of a VDT is three locales.
@{locale T1_names} is for names of constructors, @{locale T1_prjs} describes the projectors
and injectors of each constructor, and @{locale T1} combines them two.\<close>

print_locale T1_names
print_locale T1_prjs
print_locale T1





end