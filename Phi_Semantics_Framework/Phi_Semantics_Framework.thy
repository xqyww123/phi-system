section \<open>Modular Formalization of Program Semantics\<close>

text \<open>Using the Virtual Datatype, Resource Space, Fiction Space, now in this section it is
  feasible to formalize the semantics of programs modularly and extensibly.

The section first presents an empty formalization (framework) of computation states
consisting of empty types, empty values, empty resources, and empty fictions.
It serves for future formalization of any specific program semantics.

Then on this empty formalization of computation states.
The framework formalizes computations using state-error-exception monad,
supporting most of control flows and therefore most of (imperative) languages.
\<close>

theory Phi_Semantics_Framework
  imports Resource_Space Virtual_Datatype.Virtual_Datatype Debt_Axiom.Debt_Axiom
          "HOL-Library.Monad_Syntax"
  keywords "resource_space" :: thy_goal
  abbrevs "<throws>" = "\<t>\<h>\<r>\<o>\<w>\<s>"
    and "<proc>" = "\<p>\<r>\<o>\<c>"
begin


text \<open>The section provides the initial empty semantics of computation states
  serving as the base for any further substantial formalization.\<close>

subsection \<open>Type\<close>

unspecified_type TY

debt_axiomatization \<p>\<o>\<i>\<s>\<o>\<n> :: TY

subsection \<open>Value\<close>

unspecified_type VAL
instance VAL :: sep_magma ..

text \<open>The semantic value is a separation magma. It is nothing related to the semantic
  or the specification framework themselves but just to be helpful in some situation for
  formalization of some semantics such as that in aggregate the separation can represent
  concatenation of fields.\<close>


subsubsection \<open>Deep Representation of Aggregated Values\<close>

class VAL =
  fixes to_val   :: \<open>'a \<Rightarrow> VAL\<close>
    and from_val :: \<open>VAL \<Rightarrow> 'a\<close>
  assumes from_to_val[simp]: \<open>from_val (to_val x) = x\<close>

class VALs =
  fixes to_vals    :: \<open>'a \<Rightarrow> VAL list\<close>
    and from_vals  :: \<open>VAL list \<Rightarrow> 'a\<close>
  assumes from_to_vals[simp]: \<open>from_vals (to_vals x) = x\<close>

class FIX_ARITY_VALs = VALs +
  fixes vals_arity :: \<open>'a itself \<Rightarrow> nat\<close>
  assumes length_to_vals[simp]: \<open>length (to_vals x) = vals_arity TYPE('a)\<close>

instantiation VAL :: VAL begin
definition to_val_VAL :: \<open>VAL \<Rightarrow> VAL\<close> where \<open>to_val_VAL = id\<close>
definition from_val_VAL :: \<open>VAL \<Rightarrow> VAL\<close> where \<open>from_val_VAL = id\<close>
instance by standard (simp add: to_val_VAL_def from_val_VAL_def)
end

instantiation unit :: FIX_ARITY_VALs begin
definition to_vals_unit    :: \<open>unit \<Rightarrow> VAL list\<close>   where \<open>to_vals_unit v  = []\<close>
definition from_vals_unit  :: \<open>VAL list \<Rightarrow> unit\<close>   where \<open>from_vals_unit _ = ()\<close>
definition vals_arity_unit :: \<open>unit itself \<Rightarrow> nat\<close> where \<open>vals_arity_unit _ = 0\<close>
instance by standard (simp_all add: vals_arity_unit_def to_vals_unit_def)
end

instantiation VAL :: FIX_ARITY_VALs begin
definition to_vals_VAL    :: \<open>VAL \<Rightarrow> VAL list\<close>   where \<open>to_vals_VAL v  = [v]\<close>
definition from_vals_VAL  :: \<open>VAL list \<Rightarrow> VAL\<close>   where \<open>from_vals_VAL  = hd\<close>
definition vals_arity_VAL :: \<open>VAL itself \<Rightarrow> nat\<close> where \<open>vals_arity_VAL _ = 1\<close>
instance by standard (simp_all add: to_vals_VAL_def from_vals_VAL_def vals_arity_VAL_def)
end

instantiation prod :: (FIX_ARITY_VALs, FIX_ARITY_VALs) FIX_ARITY_VALs begin

definition to_vals_prod    :: \<open>'a \<times> 'b \<Rightarrow> VAL list\<close>
  where \<open>to_vals_prod v = (case v of (v1,v2) \<Rightarrow> to_vals v1 @ to_vals v2)\<close>
definition from_vals_prod  :: \<open>VAL list \<Rightarrow> 'a \<times> 'b\<close>
  where \<open>from_vals_prod vs = (@v. to_vals v = vs)\<close>
definition vals_arity_prod :: \<open>('a \<times> 'b) itself \<Rightarrow> nat\<close>
  where \<open>vals_arity_prod _ = vals_arity TYPE('a) + vals_arity TYPE('b)\<close>

instance apply standard
  apply (clarsimp simp add: to_vals_prod_def from_vals_prod_def)
  apply (smt (verit) Eps_case_prod_eq Eps_cong append_eq_append_conv from_to_vals length_to_vals split_def)
  by (clarsimp simp add: to_vals_prod_def vals_arity_prod_def)

end

instantiation list :: (VAL) VALs begin
definition to_vals_list :: \<open>'a list \<Rightarrow> VAL list\<close> where \<open>to_vals_list = map to_val\<close>
definition from_vals_list :: \<open>VAL list \<Rightarrow> 'a list\<close> where \<open>from_vals_list = map from_val\<close>
instance by standard (induct_tac x; simp add: to_vals_list_def from_vals_list_def)
end



subsection \<open>Resource\<close>

unspecified_type RES
unspecified_type RES_N
type_synonym resource = \<open>RES_N \<Rightarrow> RES\<close>
type_synonym 'T resource_entry = "(RES_N, RES, 'T) Resource_Space.kind"

setup \<open>Sign.mandatory_path "RES"\<close>

consts DOMAIN :: \<open>RES_N \<Rightarrow> RES sep_homo_set\<close>

debt_axiomatization sort: \<open>OFCLASS(RES, sep_algebra_class)\<close>

setup \<open>Sign.parent_path\<close>

instance RES :: sep_algebra using RES.sort .

setup \<open>Sign.mandatory_path "RES"\<close>

debt_axiomatization ex_RES_not_1: \<open>\<exists>r::RES. r \<noteq> 1\<close>

lemma ex_two_distinct:
  \<open>\<exists>r1 r2 :: resource. r1 \<noteq> r2\<close>
  unfolding fun_eq_iff apply simp
  by (meson RES.ex_RES_not_1)

setup \<open>Sign.parent_path\<close>

instantiation RES :: sep_carrier_1 begin
definition mul_carrier_RES :: \<open>RES \<Rightarrow> bool\<close> where \<open>mul_carrier_RES = (\<lambda>_. True)\<close>
  \<comment> \<open>As a type specially defined to represent the representation of resources, it is noisy-free.\<close>
instance by (standard; simp add: mul_carrier_RES_def)
end

interpretation RES: "resource_space" RES.DOMAIN .

ML_file \<open>resource_space_more.ML\<close>
 
ML \<open>Resource_Space.define_command \<^command_keyword>\<open>resource_space\<close> "extend resource semantics"\<close>


subsection \<open>Abnormal\<close>

unspecified_type ABNM


subsection \<open>All-in-One Semantics\<close>

debt_axiomatization Well_Type :: \<open>TY \<Rightarrow> VAL set\<close>
  where Well_Type_disjoint: \<open>ta \<noteq> tb \<Longrightarrow> Well_Type ta \<inter> Well_Type tb = {}\<close>
    and Well_Type_poison[simp]: \<open>Well_Type \<p>\<o>\<i>\<s>\<o>\<n> = {}\<close>

debt_axiomatization Can_EqCompare :: \<open>resource \<Rightarrow> VAL \<Rightarrow> VAL \<Rightarrow> bool\<close>
  where can_eqcmp_sym: "Can_EqCompare res A B \<longleftrightarrow> Can_EqCompare res B A"

consts EqCompare :: \<open>VAL \<Rightarrow> VAL \<Rightarrow> bool\<close>
(*  and   eqcmp_refl:  "EqCompare A A"
    and   eqcmp_sym:   "EqCompare A B \<longleftrightarrow> EqCompare B A"
    and   eqcmp_trans: "EqCompare A B \<Longrightarrow> EqCompare B C \<Longrightarrow> EqCompare A C" *)

debt_axiomatization Zero :: \<open>TY \<Rightarrow> VAL option\<close>
  where zero_well_typ: "pred_option (\<lambda>v. v \<in> Well_Type T) (Zero T)"

definition has_Zero :: \<open>TY \<Rightarrow> bool\<close>
  where \<open>has_Zero T \<longleftrightarrow> Zero T \<noteq> None\<close>

lemma Zero_\<p>\<o>\<i>\<s>\<o>\<n>[simp]:
  \<open> Zero \<p>\<o>\<i>\<s>\<o>\<n> = None \<close>
  by (metis Well_Type_poison empty_iff not_None_eq option.pred_inject(2) zero_well_typ)

lemma has_Zero_\<p>\<o>\<i>\<s>\<o>\<n>[simp]:
  \<open> \<not> has_Zero \<p>\<o>\<i>\<s>\<o>\<n> \<close>
  unfolding has_Zero_def
  by simp

lemma Well_Type_unique:
  \<open>v \<in> Well_Type ta \<Longrightarrow> v \<in> Well_Type tb \<Longrightarrow> ta = tb\<close>
  using Well_Type_disjoint by blast

(*
abbreviation \<open>Valid_Type T \<equiv> Satisfiable (Well_Type T)\<close>*)


subsection \<open>Formalization of Computation\<close>

subsubsection \<open>Explicit Annotation of Semantic Arguments and Returns\<close>

text \<open>Arguments and Returns are wrapped by \<phi>arg type.
  It helps the programming framework and syntax parser to recognize which one is an argument
  or a return, among values that may be used for other purposes of specification.\<close>

datatype 'a \<phi>arg = \<phi>arg (dest: 'a)
hide_const (open) dest


definition unreachable :: \<open>'a::VALs\<close> where \<open>unreachable = undefined\<close>

lemma \<phi>arg_forall: \<open>All P \<longleftrightarrow> (\<forall>x. P (\<phi>arg x))\<close> by (metis \<phi>arg.exhaust)
lemma \<phi>arg_exists: \<open>Ex P  \<longleftrightarrow> (\<exists>x. P (\<phi>arg x))\<close> by (metis \<phi>arg.exhaust)
lemma \<phi>arg_All: \<open>(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (\<phi>arg x))\<close>
proof
  fix x :: 'a assume A: \<open>(\<And>x. PROP P x)\<close> then show \<open>PROP P (\<phi>arg x)\<close> .
next
  fix x :: \<open>'a \<phi>arg\<close> assume A: \<open>\<And>x. PROP P (\<phi>arg x)\<close>
  from \<open>PROP P (\<phi>arg (\<phi>arg.dest x))\<close> show "PROP P x" by simp
qed


definition \<open>\<phi>V_none = \<phi>arg ()\<close>
definition \<phi>V_pair ("_\<^bold>, _" [11,10] 10) where \<open>\<phi>V_pair x y = \<phi>arg (\<phi>arg.dest x, \<phi>arg.dest y)\<close>
definition \<open>\<phi>V_case_prod f x \<equiv> case x of \<phi>arg (a,b) \<Rightarrow> f (\<phi>arg a) (\<phi>arg b)\<close>
definition \<open>\<phi>V_fst x = map_\<phi>arg fst x\<close>
definition \<open>\<phi>V_snd x = map_\<phi>arg snd x\<close>
abbreviation \<open>\<phi>V_nil \<equiv> \<phi>arg []\<close>
definition \<open>\<phi>V_cons h l = \<phi>arg (\<phi>arg.dest h # \<phi>arg.dest l)\<close>
definition \<open>\<phi>V_hd l = \<phi>arg (hd (\<phi>arg.dest l))\<close>
definition \<open>\<phi>V_tl l = \<phi>arg (tl (\<phi>arg.dest l))\<close>

lemma \<phi>V_simps[simp]:
  \<open>\<phi>V_pair (\<phi>V_fst v) (\<phi>V_snd v) = v\<close>
  \<open>\<phi>V_fst (\<phi>V_pair u y) = u\<close>
  \<open>\<phi>V_snd (\<phi>V_pair x u) = u\<close>
  \<open>\<phi>V_fst (\<phi>arg (xa,xb)) = \<phi>arg xa\<close>
  \<open>\<phi>V_snd (\<phi>arg (xa,xb)) = \<phi>arg xb\<close>
  \<open>\<phi>V_cons (\<phi>arg h) (\<phi>arg l) = \<phi>arg (h#l)\<close>
  \<open>\<phi>V_hd (\<phi>V_cons hv lv) = hv\<close>
  \<open>\<phi>V_tl (\<phi>V_cons hv lv) = lv\<close>
  \<open>\<phi>V_case_prod f (\<phi>V_pair a b) = f a b\<close>
  \<open>\<phi>V_case_prod f = (\<lambda>v. f (\<phi>V_fst v) (\<phi>V_snd v))\<close>
(*  \<open>\<phi>V_case_prod (\<lambda>a b. f2 (\<phi>V_pair a b)) = f2\<close>
  \<open>\<phi>V_case_prod (\<lambda>a. \<phi>V_case_prod (\<lambda>b c. f3 (\<phi>V_pair a (\<phi>V_pair b c)))) = f3\<close>
  \<open>\<phi>V_case_prod (\<lambda>a. \<phi>V_case_prod (\<lambda>b. \<phi>V_case_prod (\<lambda>c d. f4 (\<phi>V_pair a (\<phi>V_pair b (\<phi>V_pair c d)))))) = f4\<close> *)
  unfolding \<phi>V_pair_def \<phi>V_fst_def \<phi>V_snd_def \<phi>V_cons_def \<phi>V_hd_def \<phi>V_tl_def \<phi>V_case_prod_def
    apply (cases v, simp)
    apply (cases v, simp)
    apply (cases v, simp)
    apply simp apply simp apply simp
    apply simp apply simp apply simp
    apply (simp add: fun_eq_iff \<phi>arg_forall) .


paragraph \<open>More auxiliary properties\<close>

lemma split_paired_All_\<phi>arg:
  "(\<forall>x. P x) \<longleftrightarrow> (\<forall>a b. P (\<phi>V_pair a b))"
  by (metis \<phi>V_simps(1))

lemma split_paired_Ex_\<phi>arg:
  "(\<exists>x. P x) \<longleftrightarrow> (\<exists>a b. P (\<phi>V_pair a b))"
  by (metis \<phi>V_simps(1))

lemma split_paired_all_\<phi>arg:
  "(\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (\<phi>V_pair a b))"
  unfolding \<phi>arg_All \<phi>V_pair_def split_paired_all by simp

lemma split_paired_All_\<phi>arg_unit:
  "(\<forall>x. P x) \<longleftrightarrow> P \<phi>V_none"
  by (simp add: \<phi>arg_forall \<phi>V_none_def)

lemma split_paired_Ex_\<phi>arg_unit:
  "(\<exists>x. P x) \<longleftrightarrow> P \<phi>V_none"
  by (simp add: \<phi>arg_exists \<phi>V_none_def)

lemma split_paired_all_\<phi>arg_unit:
  "(\<And>x. PROP P x) \<equiv> PROP P \<phi>V_none"
  unfolding \<phi>arg_All \<phi>V_pair_def split_paired_all \<phi>V_none_def by simp




(* datatype unreachable = unreachable

instantiation unreachable :: VALs begin
definition to_vals_unreachable :: \<open>unreachable \<Rightarrow> VAL list\<close> where \<open>to_vals_unreachable _ = undefined\<close>
definition from_vals_unreachable :: \<open>VAL list \<Rightarrow> unreachable\<close> where \<open>from_vals_unreachable _ = unreachable\<close>
definition vals_arity_unreachable :: \<open>unreachable itself \<Rightarrow> nat\<close>
  where \<open>vals_arity_unreachable _ = length (undefined::VAL list)\<close>

instance apply standard
  apply (simp_all add: to_vals_unreachable_def from_vals_unreachable_def vals_arity_unreachable_def)
  by (metis unreachable.exhaust)
end
*)

paragraph \<open>Syntax\<close>

notation (do_notation) \<phi>V_fst ("_\<^sub>'(\<^sub>1\<^sub>')")
                   and \<phi>V_snd ("_\<^sub>'(\<^sub>2\<^sub>')")


subsubsection \<open>Monadic Formalization\<close>

text \<open>\<open>('ret,'ex,'RES_N,'RES) state\<close> represents any potential returning state of a program.

\<^item> \<open>Success v r\<close> represents a successful returning state with return value \<open>v\<close> and resulted resource
  state \<open>r\<close>.

\<^item> \<open>Abnormal v r\<close> represents the computation throws an exception of value \<open>v\<close>, at the
  moment when the state of the resources is \<open>r\<close>.

\<^item> \<open>NonTerm\<close> represents the execution does not terminate.

\<^item> \<open>Invalid\<close> represents the computation is invalid.
  It defines the domain of valid programs, which are the ones that never never generates
  an execution path that results in \<open>Invalid\<close>.

\<^item> \<open>Assumption_Violated\<close> represents the computation that results in an execution path that is not
  considered or modelled by the trust base.
  For example, the formalization of the allocation instruction may assume the size of the object
  to be allocated is always less than the size of the address space (e.g., \<open>2\<^sup>3\<^sup>2\<close> bytes).
  In another case users may assume the size of their objects is representable by \<open>\<s>\<i>\<z>\<e>_\<t>\<close>.
  \<open>Assumption_Violated\<close> enables an easy way for semantic assumptions, e.g., to assume \<open>P\<close>,
  \[ \<open>if P then do-something else return Assumption_Violated\<close> \]
  \<open>Assumption_Violated\<close> is admitted by any post-condition, i.e.,
  \[ {\<top>} return Assumption_Violated {\<bottom>} \]
  Computations returning \<open>Assumption_Violated\<close> are trusted by the trust base.
  This additional increment in the trust base is controllable, because whether and where to
  use the \<open>Assumption_Violated\<close>, this is determined by the formalization of instruction semantics,
  which belongs to the trust base already.
\<close>

declare [ [typedef_overloaded] ]

datatype 'ret comp =
      Success \<open>'ret \<phi>arg\<close> (resource: resource)
    | Abnormal \<open>ABNM\<close> (resource: resource)
    | Invalid (*TODO: rename to Stuck*)
    | AssumptionBroken
    | NonTerm (*TODO: rename to NonTerminating*)

declare [ [typedef_overloaded = false] ]


lemma split_comp_All:
  \<open>All P \<longleftrightarrow> (\<forall>v r. P (Success v r)) \<and> (\<forall>v r. P (Abnormal v r)) \<and> P Invalid
                \<and> P AssumptionBroken \<and> P NonTerm\<close>
  by (metis comp.exhaust)

lemma split_comp_Ex:
  \<open>Ex P \<longleftrightarrow> (\<exists>v r. P (Success v r)) \<or> (\<exists>v r. P (Abnormal v r)) \<or> P Invalid
                \<or> P AssumptionBroken \<or> P NonTerm\<close>
  by (metis comp.exhaust)

hide_const(open) resource

declare comp.split[split]

text \<open>Procedure is the basic building block of a program on the semantics formalization.
It represents a segment of a program, which is defined inductively,

\<^item> Any instruction instantiated by any arguments is a procedure
\<^item> Any lambda abstraction of a procedure is a procedure
\<^item> Sequential composition \<open>f \<bind> g\<close> is a procedure iff \<open>f, g\<close> are procedures.
\<^item> A control flow combinator combines several procedures into a procedure

Control flow combinator does not include the sequential composition combinator \<open>\<bind>\<close>.

Any function, routine, or sub-routine in high level languages is a procedure but a procedure
does not necessarily corresponds to them nor any basic block in assemble representations.

A procedure is not required to be a valid program necessarily.
Procedure is only a syntax structure and the semantics of invalid operations or programs
is expressed by returning \<open>Invalid\<close>.

%% Not Required:
% \<^bold>\<open>Normal Form of Procedures\<close> (NFP) is defined by the following BNF,
% \begin{align}
% \<open>NFP p\<close> \Coloneqq & \<open>return v\<close>
%                 | & \<open>i \<bind> p\<close>   & &\text{for \<open>i \<in> Instructions\<close>} \\
%                 | & \<open>\<lambda>x. p\<close>
%                 | & \<open>c p p \<cdots> p\<close> & &\text{\<open>c\<close> is a control flow combinator.}
% \end{align}
% It essentially says any lambda abstraction occurring in the left hand side of a sequential
% composition \<open>(\<lambda>x. f) \<bind> g\<close> can be expanded to the whole term, i.e., \<open>\<lambda>x. (f \<bind> g)\<close>.
% And any body of the control flows is also in NFP.
% It is obvious the NFP can express equivalently any procedure.
% NFP is used later in CoP to construct any procedure.

% TODO: value annotation and slightly-shallow representation.
 \<close>

type_synonym 'ret proc = "resource \<Rightarrow> 'ret comp set"
type_synonym ('arg,'ret) proc' = "'arg \<phi>arg \<Rightarrow> 'ret proc"

definition bind :: "'a proc \<Rightarrow> ('a,'b) proc' \<Rightarrow> 'b proc"
  where "bind f g = (\<lambda>res. \<Union>((\<lambda>y. case y of Success v x \<Rightarrow> g v x
                                           | Abnormal v x \<Rightarrow> {Abnormal v x}
                                           | Invalid \<Rightarrow> {Invalid}
                                           | NonTerm \<Rightarrow> {NonTerm}
                                           | AssumptionBroken \<Rightarrow> {AssumptionBroken}
                              ) ` f res))" 


adhoc_overloading Monad_Syntax.bind bind

definition \<open>det_lift f x = {f x}\<close>

definition Return ("\<r>\<e>\<t>\<u>\<r>\<n>")
  where \<open>Return = det_lift o Success\<close>

definition Nondet :: \<open>'ret proc \<Rightarrow> 'ret proc \<Rightarrow> 'ret proc\<close>
  where \<open>Nondet f g = (\<lambda>res. f res \<union> g res)\<close>

term \<open>f \<bind> Return\<close>
term \<open>do { x <- (f::'a proc); Return xaa }\<close>

lemma proc_bind_SKIP'[simp]:
  "f \<bind> Return \<equiv> f"
  "Return any \<bind> ff \<equiv> ff any"
  "(g \<then> Return any) \<then> f \<equiv> g \<then> f"
  "(\<lambda>v. Return v \<bind> h) \<equiv> h"
  unfolding bind_def atomize_eq fun_eq_iff det_lift_def set_eq_iff Return_def
  by (clarsimp; metis comp.exhaust)+

lemma proc_bind_return_none[simp]:
  "f_nil \<then> Return \<phi>V_none \<equiv> f_nil"
  for f_nil :: \<open>unit proc\<close>
  unfolding bind_def atomize_eq fun_eq_iff det_lift_def set_eq_iff Return_def \<phi>V_none_def
  apply (clarsimp)
  subgoal for x y
  apply rule
    apply clarsimp
    subgoal for z
      apply (cases z; simp add: \<phi>arg_All) .
  apply (rule bexI[where x=y]; clarsimp simp add: \<phi>arg_All) . .

lemmas proc_bind_SKIP[simp] =
  proc_bind_SKIP'[unfolded Return_def, simplified]
  proc_bind_return_none[unfolded Return_def, simplified]

lemma proc_bind_assoc[simp]:
  "((A \<bind> B) \<bind> C) = (A \<bind> (\<lambda>x. B x \<bind> C))" for A :: \<open>'a proc\<close>
  unfolding bind_def fun_eq_iff det_lift_def set_eq_iff
  by clarsimp


definition Valid_Proc :: \<open>'ret proc \<Rightarrow> bool\<close>
  where \<open>Valid_Proc f \<longleftrightarrow> (\<forall>v s s'. Success v s' \<in> f s \<and> s \<in> RES.SPACE \<longrightarrow> s' \<in> RES.SPACE)
                             \<and> (\<forall>e s s'. Abnormal e s' \<in> f s \<and> s \<in> RES.SPACE \<longrightarrow> s' \<in> RES.SPACE)\<close>

lemma Valid_Proc_bind:
  \<open> Valid_Proc f
\<Longrightarrow> (\<And>v. Valid_Proc (g v))
\<Longrightarrow> Valid_Proc (f \<bind> g)\<close>
  unfolding Valid_Proc_def bind_def
  subgoal premises prems
    apply (clarsimp; rule; clarsimp)
    apply (case_tac x; simp add: Bex_def split_comp_Ex)
    using prems(1) prems(2) apply blast
    apply (case_tac x; simp add: Bex_def split_comp_Ex)
    using prems(1) prems(2) apply blast
    using prems(1) by blast .
  


end
