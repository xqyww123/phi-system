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
  imports Main Resource_Space Debt_Axiom.Debt_Axiom
  abbrevs "<:>" = "\<Ztypecolon>"
    and "<throws>" = "\<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s"
    and "<proc>" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
    and "<view>" = "\<^bold>v\<^bold>i\<^bold>e\<^bold>w"
    and "<with>" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
begin


text \<open>The section provides the initial empty semantics of computation states
  serving as the base for any further substantial formalization.\<close>

subsection \<open>Type\<close>

virtual_datatype \<phi>empty_ty \<comment> \<open>base of type formalization\<close>

unspecified_type TY
unspecified_type TY_N
type_synonym 'T type_entry = \<open>(TY_N, TY, 'T) Virtual_Datatype.Field\<close>

consts TY_CONS_OF :: \<open>TY \<Rightarrow> TY_N\<close>

interpretation \<phi>empty_ty TY_CONS_OF by standard simp


subsection \<open>Value\<close>

virtual_datatype \<phi>empty_val :: sep_magma \<comment> \<open>base of value formalization\<close>

unspecified_type VAL
unspecified_type VAL_N
type_synonym 'T value_entry = \<open>(VAL_N, VAL, 'T) Virtual_Datatype.Field\<close>

consts VAL_CONS_OF :: \<open>VAL \<Rightarrow> VAL_N\<close>

instance VAL :: sep_magma ..

interpretation \<phi>empty_val VAL_CONS_OF by standard simp


subsubsection \<open>Deep Representation of Values of Variable Length\<close>


class VALs =
  fixes to_vals    :: \<open>'a \<Rightarrow> VAL list\<close>
    and from_vals  :: \<open>VAL list \<Rightarrow> 'a\<close>
    and vals_arity :: \<open>'a itself \<Rightarrow> nat\<close>
  assumes from_to_vals[simp]: \<open>from_vals (to_vals x) = x\<close>
    and length_to_vals[simp]: \<open>length (to_vals x) = vals_arity TYPE('a)\<close>

instantiation VAL :: VALs begin
definition to_vals_VAL    :: \<open>VAL \<Rightarrow> VAL list\<close>   where \<open>to_vals_VAL v  = [v]\<close>
definition from_vals_VAL  :: \<open>VAL list \<Rightarrow> VAL\<close>   where \<open>from_vals_VAL  = hd\<close>
definition vals_arity_VAL :: \<open>VAL itself \<Rightarrow> nat\<close> where \<open>vals_arity_VAL _ = 1\<close>
instance by standard (simp_all add: to_vals_VAL_def from_vals_VAL_def vals_arity_VAL_def)
end

instantiation prod :: (VALs, VALs) VALs begin

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
  



subsection \<open>Resource\<close>

resource_space \<phi>empty_res \<comment> \<open>base of resource formalization\<close>

unspecified_type RES
unspecified_type RES_N
type_synonym resource = \<open>RES_N \<Rightarrow> RES\<close>

debt_axiomatization RES_sort: \<open>OFCLASS(RES, sep_algebra_class)\<close>

instance RES :: sep_algebra using RES_sort .

interpretation \<phi>empty_res \<open>TYPE(RES_N)\<close> \<open>TYPE(RES)\<close> by standard simp

debt_axiomatization Resource_Validator :: \<open>RES_N \<Rightarrow> RES set\<close>
  where Resource_Validator_mult_homo:
      \<open>\<And>N. A N ## B N \<Longrightarrow> A N * B N \<in> Resource_Validator N \<longleftrightarrow> A N \<in> Resource_Validator N \<and> B N \<in> Resource_Validator N\<close>
  and   Resource_Validator_1: \<open>\<And>N. 1 \<in> Resource_Validator N\<close>

definition "Valid_Resource = {R. (\<forall>N. R N \<in> Resource_Validator N)}"

lemma Valid_Resource_1[iff]:
  \<open>1 \<in> Valid_Resource\<close>
  unfolding Valid_Resource_def by (simp add: Resource_Validator_1)

lemma Valid_Resource_mult_homo:
  \<open>A ## B \<Longrightarrow> A * B \<in> Valid_Resource \<longleftrightarrow> A \<in> Valid_Resource \<and> B \<in> Valid_Resource\<close>
  unfolding Valid_Resource_def
  by (simp add: times_fun sep_disj_fun_def Resource_Validator_mult_homo; blast)


subsection \<open>Exception\<close>

virtual_datatype \<phi>empty_abnormal

unspecified_type ERR
unspecified_type ERR_N
type_synonym 'T error_entry = \<open>(ERR_N, ERR, 'T) Virtual_Datatype.Field\<close>

consts ERR_CONS_OF :: \<open>ERR \<Rightarrow> ERR_N\<close>

interpretation \<phi>empty_abnormal ERR_CONS_OF by standard simp


subsection \<open>All-in-One Semantics\<close>

debt_axiomatization Well_Type :: \<open>TY \<Rightarrow> VAL set\<close>
  where Well_Type_disjoint: \<open>ta \<noteq> tb \<Longrightarrow> Well_Type ta \<inter> Well_Type tb = {}\<close>

debt_axiomatization Can_EqCompare :: \<open>resource \<Rightarrow> VAL \<Rightarrow> VAL \<Rightarrow> bool\<close>
  where can_eqcmp_sym: "Can_EqCompare res A B \<longleftrightarrow> Can_EqCompare res B A"

consts EqCompare :: \<open>VAL \<Rightarrow> VAL \<Rightarrow> bool\<close>
(*  and   eqcmp_refl:  "EqCompare A A"
    and   eqcmp_sym:   "EqCompare A B \<longleftrightarrow> EqCompare B A"
    and   eqcmp_trans: "EqCompare A B \<Longrightarrow> EqCompare B C \<Longrightarrow> EqCompare A C" *)

debt_axiomatization Zero :: \<open>TY \<Rightarrow> VAL option\<close>
  where zero_well_typ: "pred_option (\<lambda>v. v \<in> Well_Type T) (Zero T)"

lemma Well_Type_unique:
  \<open>v \<in> Well_Type ta \<Longrightarrow> v \<in> Well_Type tb \<Longrightarrow> ta = tb\<close>
  using Well_Type_disjoint by blast

abbreviation \<open>Valid_Type T \<equiv> Inhabited (Well_Type T)\<close>


subsection \<open>Fiction\<close>

unspecified_type FIC
unspecified_type FIC_N

type_synonym fiction = \<open>FIC_N \<Rightarrow> FIC\<close>
type_synonym  assn = \<open>fiction set\<close>
type_synonym rassn = \<open>resource set\<close>
type_synonym vassn = \<open>VAL set\<close>

debt_axiomatization FIC_sort: \<open>OFCLASS(FIC, sep_algebra_class)\<close>

instance FIC :: sep_algebra using FIC_sort .

consts INTERPRET :: \<open>FIC_N \<Rightarrow> (FIC, resource) interp\<close>

interpretation fictional_space INTERPRET .

definition "INTERP_RES fic \<equiv> Valid_Resource \<inter> {_. Fic_Space fic} \<inter> \<I> INTERP fic"
  \<comment> \<open>Interpret a fiction\<close>

lemma In_INTERP_RES:
  \<open>r \<in> INTERP_RES fic \<longleftrightarrow> r \<in> Valid_Resource \<and> Fic_Space fic \<and> r \<in> \<I> INTERP fic\<close>
  unfolding INTERP_RES_def by simp

definition INTERP_SPEC :: \<open>assn \<Rightarrow> rassn\<close>
  \<comment> \<open>Interpret a fictional specification\<close>
  where "INTERP_SPEC T = { res. \<exists>fic. fic \<in> T \<and> res \<in> INTERP_RES fic }"

lemma INTERP_SPEC:
  \<open>res \<in> INTERP_SPEC T \<longleftrightarrow> (\<exists>fic. fic \<in> T \<and> res \<in> INTERP_RES fic)\<close>
  unfolding INTERP_SPEC_def by simp

lemma INTERP_SPEC_subset[intro, simp]: \<open>A \<subseteq> B \<Longrightarrow> INTERP_SPEC A \<subseteq> INTERP_SPEC B\<close>
  unfolding INTERP_SPEC_def subset_iff by simp blast

lemma INTERP_SPEC_plus[iff]:
  \<open>INTERP_SPEC (A + B) = INTERP_SPEC A + INTERP_SPEC B\<close>
  unfolding INTERP_SPEC_def plus_set_def by simp blast

lemma INTERP_SPEC_empty[intro, simp]:
  \<open>S = {} \<Longrightarrow> INTERP_SPEC S = {}\<close>
  unfolding INTERP_SPEC_def set_eq_iff by simp

lemma INTERP_SPEC_0[simp]:
  \<open>INTERP_SPEC 0  = 0\<close>
  \<open>INTERP_SPEC {} = {}\<close>
  unfolding INTERP_SPEC_def zero_set_def by simp+

lemma INTERP_mult:
  \<open> Fic_Space f1
\<Longrightarrow> Fic_Space f2
\<Longrightarrow> dom1 r1 \<inter> dom1 r2 = {}
\<Longrightarrow> dom1 f1 \<inter> dom1 f2 = {}
\<Longrightarrow> r1 \<in> \<I> INTERP f1
\<Longrightarrow> r2 \<in> \<I> INTERP f2
\<Longrightarrow> f1 ## f2
\<Longrightarrow> r1 * r2 \<in> \<I> INTERP (f1 * f2) \<and> r1 ## r2\<close>
  unfolding INTERP_def Fic_Space_def
  by (simp add: dom1_sep_mult_disjoint times_fun prod.union_disjoint
                disjoint_dom1_eq_1[of f1 f2],
      meson dom1_disjoint_sep_disj times_set_I)


subsection \<open>Formalization of Computation\<close>

subsubsection \<open>Explicit Annotation of Semantic Arguments and Returns\<close>

text \<open>Arguments and Returns are wrapped by sem type.
  For sure this wrap is not necessary, but it helps the programming framework and syntax parser
  to recognize which entity is an argument or a return.\<close>

datatype 'a sem = sem (dest: 'a)
hide_const (open) dest
typedecl unreachable

lemma sem_value_forall: \<open>All P \<longleftrightarrow> (\<forall>x. P (sem x))\<close> by (metis sem.exhaust)
lemma sem_value_exists: \<open>Ex P  \<longleftrightarrow> (\<exists>x. P (sem x))\<close> by (metis sem.exhaust)
lemma sem_value_All: \<open>(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (sem x))\<close>
proof
  fix x :: 'a assume A: \<open>(\<And>x. PROP P x)\<close> then show \<open>PROP P (sem x)\<close> .
next
  fix x :: \<open>'a sem\<close> assume A: \<open>\<And>x. PROP P (sem x)\<close>
  from \<open>PROP P (sem (sem.dest x))\<close> show "PROP P x" by simp
qed

abbreviation \<open>\<phi>V_none \<equiv> sem ()\<close>
definition \<open>\<phi>V_pair x y = sem (sem.dest x, sem.dest y)\<close>
definition \<open>\<phi>V_fst x = map_sem fst x\<close>
definition \<open>\<phi>V_snd x = map_sem snd x\<close>
abbreviation \<open>\<phi>V_nil \<equiv> sem []\<close>
definition \<open>\<phi>V_cons h l = sem (sem.dest h # sem.dest l)\<close>
definition \<open>\<phi>V_hd l = sem (hd (sem.dest l))\<close>
definition \<open>\<phi>V_tl l = sem (tl (sem.dest l))\<close>

lemma \<phi>V_simps[simp]:
  \<open>\<phi>V_pair (\<phi>V_fst v) (\<phi>V_snd v) = v\<close>
  \<open>\<phi>V_fst (\<phi>V_pair u y) = u\<close>
  \<open>\<phi>V_snd (\<phi>V_pair x u) = u\<close>
  \<open>\<phi>V_cons (sem h) (sem l) = sem (h#l)\<close>
  \<open>\<phi>V_hd (\<phi>V_cons hv lv) = hv\<close>
  \<open>\<phi>V_tl (\<phi>V_cons hv lv) = lv\<close>
  unfolding \<phi>V_pair_def \<phi>V_fst_def \<phi>V_snd_def \<phi>V_cons_def \<phi>V_hd_def \<phi>V_tl_def
     apply (cases v, simp)
     apply (cases v, simp)
     apply (cases v, simp)
    apply simp apply simp apply simp .


subsubsection \<open>Monadic Formalization\<close>

text \<open>\<open>('ret,'ex,'RES_N,'RES) state\<close> represents any potential returning state of a program.

\<^item> \<open>Success v r\<close> represents a successful returning state with return value \<open>v\<close> and resulted resource
  state \<open>r\<close>.

\<^item> \<open>Exception v r\<close> represents the computation throws an exception of value \<open>v\<close>, at the
  moment when the state of the resources is \<open>r\<close>.

\<^item> \<open>NonTerm\<close> represents the execution does not terminate.

\<^item> \<open>Invalid\<close> represents the computation is invalid.
  It defines the domain of valid programs, which are the ones that never never generates
  an execution path that results in \<open>Invalid\<close>.
 
\<^item> \<open>Assumption_Violated\<close> represents the computation that results in an execution path that is not
  considered or modelled by the trust base.
  For example, the formalization of the allocation instruction may assume the size of the object
  to be allocated is always less than the size of the address space (e.g., \<open>2\<^sup>3\<^sup>2\<close> bytes).
  In another case users may assume the size of their objects is representable by \<open>size_t\<close>.
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

datatype 'ret state =
      Success \<open>'ret sem\<close> (resource: resource)
    | Exception \<open>ERR sem\<close> (resource: resource)
    | Invalid | PartialCorrect

declare [ [typedef_overloaded = false] ]


lemma split_state_All:
  \<open>All P \<longleftrightarrow> (\<forall>v r. P (Success v r)) \<and> (\<forall>v r. P (Exception v r)) \<and> P Invalid \<and> P PartialCorrect\<close>
  by (metis state.exhaust)

lemma split_state_Ex:
  \<open>Ex P \<longleftrightarrow> (\<exists>v r. P (Success v r)) \<or> (\<exists>v r. P (Exception v r)) \<or> P Invalid \<or> P PartialCorrect\<close>
  by (metis state.exhaust)  

hide_const(open) resource

declare state.split[split]

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

type_synonym 'ret proc = "resource \<Rightarrow> 'ret state set"
type_synonym ('arg,'ret) proc' = "'arg sem \<Rightarrow> 'ret proc"


definition bind :: "'a proc \<Rightarrow> ('a,'b) proc' \<Rightarrow> 'b proc"  ("_ \<bind>/ _" [75,76] 75)
  where "bind f g = (\<lambda>res. \<Union>((\<lambda>y. case y of Success v x \<Rightarrow> g v x
                                           | Exception v x \<Rightarrow> {Exception v x}
                                           | Invalid \<Rightarrow> {Invalid}
                                           | PartialCorrect \<Rightarrow> {PartialCorrect}) ` f res))"

abbreviation bind' ("_ \<ggreater>/ _" [75,76] 75)
  where \<open>bind' f g \<equiv> (f \<bind> (\<lambda>_. g))\<close>

definition \<open>det_lift f x = {f x}\<close>

definition \<open>Return = det_lift o Success\<close>

definition Nondet :: \<open>'ret proc \<Rightarrow> 'ret proc \<Rightarrow> 'ret proc\<close>
  where \<open>Nondet f g = (\<lambda>res. f res \<union> g res)\<close>

lemma proc_bind_SKIP'[simp]:
  "f \<bind> Return \<equiv> f"
  "Return any \<bind> ff \<equiv> ff any"
  "(g \<ggreater> Return any) \<ggreater> f \<equiv> g \<ggreater> f"
  "(\<lambda>v. Return v \<bind> h) \<equiv> h"
  unfolding bind_def atomize_eq fun_eq_iff det_lift_def set_eq_iff Return_def
  by (clarsimp; metis state.exhaust)+

lemma proc_bind_return_none[simp]:
  "f_nil \<ggreater> Return \<phi>V_none \<equiv> f_nil"
  for f_nil :: \<open>unit proc\<close>
  unfolding bind_def atomize_eq fun_eq_iff det_lift_def set_eq_iff Return_def
  apply (clarsimp)
  subgoal for x y
  apply rule
    apply clarsimp
    subgoal for z
      apply (cases z; simp add: sem_value_All) .
  apply (rule bexI[where x=y]; clarsimp simp add: sem_value_All) . .

lemmas proc_bind_SKIP[simp] =
  proc_bind_SKIP'[unfolded Return_def, simplified]
  proc_bind_return_none[unfolded Return_def, simplified]

lemma proc_bind_assoc[simp]:
  "((A \<bind> B) \<bind> C) = (A \<bind> (\<lambda>x. B x \<bind> C))"
  unfolding bind_def fun_eq_iff det_lift_def set_eq_iff
  by clarsimp

end
