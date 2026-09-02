theory Debt_Axiom_Doc
  imports Main Debt_Axiom.Debt_Axiom
begin

section \<open>Introduction over an Example\<close>

text \<open>Debt Axiom provides an approach to safely declare an axiom early, build anything above
  the axiom, and later prove the validity of the previously declared axiom.
  The declared axioms are not free, but require certificates later.
  They are recorded in a ledger so we name them, \<^emph>\<open>debt axioms\<close>.
  A ML kernel validates the certificate and especially it does not depend on
  any declared debt axioms, so the certification is valid and it is a safe way to declare axioms.
  The ML kernel is tiny, consisting of 30 lines of code only, and depending only on
  Isabelle's kernel.

  It resembles Locale which enables local assumptions, but we do not use locales and they are
  real axioms, so we circumvent the limitations of Locale like incomplete supports for some
  Isabelle functions like syntax translation, and complexity of multi-dependence especially
  when the hierarchy is complicated, and also performance cost during activating a huge locale
  when using @{command context} command and \<open>(in locale)\<close> syntax.

  An example usage of the library is building an extensible modular semantic library, where
  we pre-build small snippets each of which formalizes a specific semantic feature,
  and we assemble the snippets of all the semantic features of a target language
  when we are going to formalize it.
  Each snippet can be an Isabelle theory and in the final assembly we import only the features that
  the target language needs.

  If we follow a deep embedding approach where two semantic types are used to model the type
    and the value of the language respectively, note,
  in such a generic library supporting free plug-in of various semantic features,
  the actual definition of the semantic types cannot be decided until the final target language
  to be formalized is given, because the complete semantic features are not decided until
  that time.


  However, if we want the library to be really useful by providing some reasoning supports and
    automatic mechanisms, we do need first the declarations of the semantic types,
    and partial definition about the semantic feature concerned by the module,
    so that we can provide some mechanisms for the feature.

  The Debt Axiom package addresses
  The tour starts from declaring semantic types used in our library to model the type
    and the value of the language respectively.

  Therefore, we just \<^emph>\<open>declare\<close> the types in an \<^emph>\<open>unspecified\<close> way.
\<close>

unspecified_type VAL

text \<open>They are unspecified meaning they are just declared but not finally defined.
The definition can be given later after the final target language is given and decides
the complete target semantic features.

We continue declare some basic infrastructure in the formalization.
\<open>typ_of\<close> give the type of a
\<close>


text \<open>Then we build a semantic module for integer value and its arithmetic.
In a new theory file for this feature, we declare the constructor of the integer model and also
its destructor.
\<close>

debt_axiomatization mk_int :: \<open>int \<Rightarrow> VAL\<close>
               and dest_int :: \<open>VAL \<Rightarrow> int\<close>
              where mk_int_inj[simp]: \<open>dest_int (mk_int i) = i\<close>

text \<open>\<open>dest_int\<close> should be the inverse function of \<open>mk_int\<close>. We declare this property by a debt
  axiom, and require the final semantic assembly to discharge the proof of the axiom.
  The @{command print_debt_axiom} now lists \<open>dest_int\<close> as an obligation debt.
\<close>

print_debt_axiom
  \<comment> \<open>\<open>\<And>i. dest_int (mk_int i) = i\<close>\<close>

text \<open>Formalization of instructions and various automation can be built above the semantic models.\<close>

definition \<open>op_add va vb = mk_int (dest_int va + dest_int vb)\<close>

lemma \<open>op_add (mk_int (1::int)) (op_add (mk_int 2) (mk_int 3)) = mk_int 6\<close>
  unfolding op_add_def by simp

text \<open>Meantime, we may formalize array in another theory file.\<close>

debt_axiomatization mk_array :: \<open>VAL list \<Rightarrow> VAL\<close>
              and dest_array :: \<open>VAL \<Rightarrow> VAL list\<close>
  where mk_array_inj[simp]: \<open>dest_array (mk_array x) = x\<close>

definition \<open>op_push v vL = mk_array (v # dest_array vL)\<close>
definition \<open>op_peek vL = hd (dest_array vL)\<close>
definition \<open>op_pop  vL = mk_array (tl (dest_array vL))\<close>

lemma \<open>op_peek (op_push v L) = v\<close>
  unfolding op_peek_def op_push_def by simp

text \<open>Now in the final theory file assembling the semantic modules,
  we instantiate the unspecified constants and discharge the debt axioms.\<close>

datatype val = V_int (dest_V_int: int) | V_array (dest_V_array: \<open>val list\<close>)

specify_type VAL[simp]: VAL = val

print_debt_axiom

specification (mk_int dest_int mk_array dest_array)
  mk_int_def': \<open>mk_int = VAL.inj o V_int\<close>
  dest_int_def': \<open>dest_int = dest_V_int o VAL.prj\<close>
  mk_array_def': \<open>mk_array = VAL.inj o V_array o map VAL.prj\<close>
  dest_array_def': \<open>dest_array = map VAL.inj o dest_V_array o VAL.prj\<close>
  by auto

lemma mk_int_inj': \<open>dest_int (mk_int i) = i\<close>
  unfolding mk_int_def' dest_int_def' by simp

lemma [simp]: \<open>VAL.inj \<circ> VAL.prj = id\<close> by fastforce

lemma mk_array_inj': \<open>dest_array (mk_array x) = x\<close>
  unfolding mk_array_def' dest_array_def' by simp

discharge_debt_axiom mk_int_inj : mk_int_inj'
  and mk_array_inj : mk_array_inj'

print_debt_axiom \<comment> \<open>Good job! No debt axiom is recorded.\<close>


text \<open>It rejects impredicativeness properly thanking to the circular dependence checking by
  Isabelle's kernel.\<close>


section \<open>Polymorphic Debt Axioms\<close>

text \<open>Debt axioms may be polymorphic, with arbitrary sort constraints on their type
  variables.  We declare a debt over two type variables with nontrivial sorts:\<close>

debt_axiomatization le_add: \<open>x \<le> x \<and> y + 0 = y\<close>
  for x :: \<open>'a::linorder\<close> and y :: \<open>'b::comm_monoid_add\<close>

text \<open>The fact \<open>le_add\<close> is usable at any instance of its sorts, like any polymorphic
  theorem:\<close>

lemma \<open>(3::nat) \<le> 3 \<and> (b::int) + 0 = b\<close> by (rule le_add)
lemma \<open>(i::int) \<le> i \<and> (n::nat) + 0 = n\<close> by (rule le_add)

text \<open>@{command print_debt_axiom} prints the \<^emph>\<open>ledger normal form\<close> of the debt:
  the sort constraints are detached from the type variables and re-attached as
  \<open>OFCLASS\<close> premises, one premise per class.  This printed proposition is the exact
  text the ML kernel compares against the certificate at discharge time --- what you
  see is what must be proved.\<close>

print_debt_axiom
  \<comment> \<open>\<open>Debt_Axiom_Doc.le_add :
       OFCLASS('a, linorder_class) \<Longrightarrow> OFCLASS('b, comm_monoid_add_class) \<Longrightarrow>
       (\<And>x y. x \<le> x \<and> y + 0 = y)\<close>\<close>

text \<open>The type variables in the printed entry carry the \<^emph>\<open>empty\<close> sort, which the
  default printer renders indistinguishably from \<open>'a::type\<close> --- the transcript above
  is the default printer's output.  A \<open>show_sorts\<close> rendering, explicitly enabled,
  makes the empty sort \<open>'a::{}\<close> visible:\<close>

declare [[show_sorts = true]]
print_debt_axiom
  \<comment> \<open>\<open>Debt_Axiom_Doc.le_add :
       OFCLASS('a::{}, linorder_class) \<Longrightarrow> OFCLASS('b::{}, comm_monoid_add_class) \<Longrightarrow>
       (\<And>(x::'a::{}) y::'b::{}. x \<le> x \<and> y + 0 = y)\<close>\<close>
declare [[show_sorts = false]]

text \<open>A polymorphic debt is discharged like any other debt.  The certificate may be
  proved at a \<^emph>\<open>weaker\<close> sort than the debt demands --- here \<open>preorder\<close> in place of
  \<open>linorder\<close> and \<open>monoid_add\<close> in place of \<open>comm_monoid_add\<close>; the residual \<open>OFCLASS\<close>
  obligations are closed automatically through the class order.  The certificate of
  a @{command discharge_debt_axiom} must be a \<^emph>\<open>named\<close> global fact: a literal fact
  certificate (\<open>discharge_debt_axiom le_add : \<open>\<dots>\<close>\<close>) can never resolve there.\<close>

lemma le_add_cert: \<open>(x::'a::preorder) \<le> x \<and> (y::'b::monoid_add) + 0 = y\<close>
  by simp

discharge_debt_axiom le_add : le_add_cert

print_debt_axiom \<comment> \<open>Good job! No debt axiom is recorded.\<close>

end