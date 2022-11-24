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
  imports Main Resource_Space
  abbrevs "<:>" = "\<Ztypecolon>"
    and "<throws>" = "\<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s"
    and "<proc>" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
    and "<view>" = "\<^bold>v\<^bold>i\<^bold>e\<^bold>w"
    and "<with>" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
begin

subsection \<open>Empty Semantic of Computation States\<close>

text \<open>The section provides the initial empty semantics of computation states
  serving as the base for any further substantial formalization.\<close>

(*subsubsection \<open>Global Parameter\<close>

(*TODO: move this!*)
consts addrspace_bits :: "nat" \<comment> \<open>The bit length of the memory address space, in unit of bits\<close>
specification (addrspace_bits) addrspace_bits_L0: "0 < addrspace_bits" by auto
*)

subsubsection \<open>Type\<close>

virtual_datatype \<phi>empty_ty \<comment> \<open>Base of type formalization\<close>

subsubsection \<open>Value\<close>

virtual_datatype 'TY \<phi>empty_val :: "nonsepable_semigroup"
  \<comment> \<open>Base of value formalization, parameterized by \<^typ>\<open>'TY\<close> modelling the type semantics.\<close>

subsubsection \<open>Resource\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) \<phi>empty_res
  \<comment> \<open>Base of resource formalization, parametereized by \<^typ>\<open>'TY\<close> modelling the types and
    \<^typ>\<open>'VAL\<close> modelling the values.\<close>

locale \<phi>resource_sem =
  fixes Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
  assumes Resource_Validator_mult_homo:
      \<open>\<And>N. A N ## B N \<Longrightarrow> A N * B N \<in> Resource_Validator N \<longleftrightarrow> A N \<in> Resource_Validator N \<and> B N \<in> Resource_Validator N\<close>
    and   Resource_Validator_1: \<open>\<And>N. 1 \<in> Resource_Validator N\<close>
begin

definition "Valid_Resource = {R. (\<forall>N. R N \<in> Resource_Validator N)}"

lemma Valid_Resource_1[iff]:
  \<open>1 \<in> Valid_Resource\<close>
  unfolding Valid_Resource_def by (simp add: Resource_Validator_1)

lemma Valid_Resource_mult_homo:
  \<open>A ## B \<Longrightarrow> A * B \<in> Valid_Resource \<longleftrightarrow> A \<in> Valid_Resource \<and> B \<in> Valid_Resource\<close>
  unfolding Valid_Resource_def
  by (simp add: times_fun sep_disj_fun_def Resource_Validator_mult_homo; blast)

end

subsubsection \<open>All-in-One Semantics\<close>

locale \<phi>empty_sem =
  \<phi>empty_ty  where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ \<phi>empty_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ \<phi>empty_res where TYPE'VAL  = \<open>TYPE('VAL)\<close>
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('RES_N)\<close>
            and TYPE'REP  = \<open>TYPE('RES::sep_algebra)\<close>
+ \<phi>resource_sem where Resource_Validator = Resource_Validator
for TY_CONS_OF and VAL_CONS_OF
and Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES::sep_algebra set\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N => 'VAL::nonsepable_semigroup)
                \<times> ('RES_N => 'RES)) itself\<close>

fixes Well_Type :: \<open>'TY \<Rightarrow> 'VAL set\<close>
assumes Well_Type_disjoint: \<open>ta \<noteq> tb \<Longrightarrow> Well_Type ta \<inter> Well_Type tb = {}\<close>

fixes Can_EqCompare :: \<open>('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'VAL \<Rightarrow> 'VAL \<Rightarrow> bool\<close>
assumes can_eqcmp_sym: "Can_EqCompare res A B \<longleftrightarrow> Can_EqCompare res B A"

fixes EqCompare :: \<open>'VAL \<Rightarrow> 'VAL \<Rightarrow> bool\<close>
(*  and   eqcmp_refl:  "EqCompare A A"
    and   eqcmp_sym:   "EqCompare A B \<longleftrightarrow> EqCompare B A"
    and   eqcmp_trans: "EqCompare A B \<Longrightarrow> EqCompare B C \<Longrightarrow> EqCompare A C" *)

fixes Zero :: \<open>'TY \<Rightarrow> 'VAL option\<close>
assumes zero_well_typ: "pred_option (\<lambda>v. v \<in> Well_Type T) (Zero T)"
begin

lemma Well_Type_unique:
  \<open>v \<in> Well_Type ta \<Longrightarrow> v \<in> Well_Type tb \<Longrightarrow> ta = tb\<close>
  using Well_Type_disjoint by blast

abbreviation \<open>Valid_Type T \<equiv> Inhabited (Well_Type T)\<close>

end

subsubsection \<open>Fiction\<close>

locale \<phi>fiction =
  \<phi>resource_sem Resource_Validator
+ fictional_space INTERPRET
for Resource_Validator :: "'RES_N \<Rightarrow> 'RES::sep_algebra set"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra, 'RES_N \<Rightarrow> 'RES::sep_algebra) interp"
begin

definition "INTERP_RES fic \<equiv> Valid_Resource \<inter> {_. Fic_Space fic} \<inter> \<I> INTERP fic"
  \<comment> \<open>Interpret a fiction\<close>

lemma In_INTERP_RES:
  \<open>r \<in> INTERP_RES fic \<longleftrightarrow> r \<in> Valid_Resource \<and> Fic_Space fic \<and> r \<in> \<I> INTERP fic\<close>
  unfolding INTERP_RES_def by simp

definition INTERP_SPEC :: \<open>('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('RES_N \<Rightarrow> 'RES) set\<close>
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

end

subsubsection \<open>All-in-One Module\<close>

locale \<phi>empty =
  \<phi>fiction Resource_Validator INTERPRET
+ \<phi>empty_sem where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                               \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                               \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra))\<close>
             and Resource_Validator = Resource_Validator
for Resource_Validator :: "'RES_N \<Rightarrow> 'RES::sep_algebra set"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra, 'RES_N \<Rightarrow> 'RES::sep_algebra) interp"
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>


(*lemma FIC_var_split: \<open>Fic_Space fic \<Longrightarrow>
    \<I> INTERP (fic * FIC_var.mk vars) = \<I> INTERP fic * {R_var.mk vars}\<close>
  apply (subst FIC_var.interp_split; simp add: exclusive_var_def R_var.mk_homo_mult)
  by (subst FIC_var.interp_split[where f = fic]; simp add: exclusive_var_def
      set_mult_single[symmetric] mult.assoc)

lemma R_var_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    R_var.clean res \<in> Valid_Resource \<and> (\<exists>vars. res R_var.name = R_var.inject (Fine vars) \<and> finite (dom vars))\<close>
  by (subst R_var.split, simp add: Valid_Resource_def times_fun_def res_valid_var one_fine_def) blast

lemma R_var_valid_split':
   \<open>NO_MATCH (R_var.clean res') res \<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow>
    R_var.clean res \<in> Valid_Resource \<and> (\<exists>vars. res R_var.name = R_var.inject (Fine vars) \<and> finite (dom vars))\<close>
  using R_var_valid_split .
*)

(*
lemma \<open>Fic_Space fic \<Longrightarrow>
      res \<in> INTERP_RES (fic * FIC_mem.mk (1(seg := Fine (push_map idx (to_share o Mapof_Val val)))))
  \<longrightarrow> (\<exists>m v. R_mem.get res = Fine m \<and> m seg = Some v \<and> v \<in> Well_Type (segidx.layout seg) \<and> index_value idx v = val)\<close>

 
lemma \<open>Fic_Space fic \<Longrightarrow> n \<noteq> 0 \<Longrightarrow>
      res \<in> INTERP_RES (fic * FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Mapof_Val val))))))
  \<longrightarrow> (\<exists>m v. R_mem.get res = Fine m \<and> m seg = Some v \<and> v \<in> Well_Type (segidx.layout seg) \<and> index_value idx v = val)\<close>
  apply (subst FIC_mem.interp_split; simp add: share_mem_def times_set_def)
  apply (subst R_mem_valid_split)
  apply (auto simp add: R_mem.proj_homo_mult Valid_Mem_def R_mem.mult_strip_inject_011
                        mult_strip_fine_011 times_fun[where x = seg] )
  subgoal premises prems for remain_res mem remain proof -
    note [simp] = mult_strip_fine_011 times_fun[where x = seg]
    have \<open>remain seg ## mem seg\<close> using \<open>remain ## mem\<close> by (simp add: sep_disj_fun_def) 
    show ?thesis
      apply (insert \<open>\<forall>x. \<exists>y. _\<close>[THEN spec[where x = seg], simplified]
                    \<open>remain seg ## mem seg\<close>
                    \<open>\<forall>seg \<in> dom _. _\<close>[unfolded Ball_def, THEN spec[where x= seg], simplified])
      apply (auto simp add: share_val_fiction \<open>n \<noteq> 0\<close>)
      subgoal premises prems2 for other_part Val proof -
        let \<open>?lhs = ?rhs\<close> = \<open>to_share \<circ> Mapof_Val Val = other_part * push_map idx (share n (to_share \<circ> Mapof_Val val))\<close>
        from \<open>?lhs = ?rhs\<close> have \<open>strip_share o pull_map idx ?lhs = strip_share o pull_map idx ?rhs\<close> by fastforce
        note this[simplified pull_map_to_share Mapof_Val_pull strip_share_share_funcomp
                             pull_map_homo_mult pull_push_map]
        thm prems2
        term Valof_Map

  thm times_fun[where x = seg]
  thm R_mem.split

*)



(* type_synonym logaddr = "nat memaddr" *)

subsection \<open>Formalization of Computation\<close>

subsubsection \<open>Explicit Annotation of Semantic Arguments and Returns\<close>

text \<open>Arguments and Returns are wrapped by sem_value type.
  For sure this wrap is not necessary, but it helps the programming framework and syntax parser
  to recognize which entity is an argument or a return.\<close>

datatype 'a sem_value = sem_value (dest_sem_value: 'a)
typedecl unreachable

lemma sem_value_forall: \<open>All P \<longleftrightarrow> (\<forall>x. P (sem_value x))\<close> by (metis sem_value.exhaust)
lemma sem_value_exists: \<open>Ex P  \<longleftrightarrow> (\<exists>x. P (sem_value x))\<close> by (metis sem_value.exhaust)
lemma sem_value_All: \<open>(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (sem_value x))\<close>
proof
  fix x :: 'a assume A: \<open>(\<And>x. PROP P x)\<close> then show \<open>PROP P (sem_value x)\<close> .
next
  fix x :: \<open>'a sem_value\<close> assume A: \<open>\<And>x. PROP P (sem_value x)\<close>
  from \<open>PROP P (sem_value (dest_sem_value x))\<close> show "PROP P x" by simp
qed

abbreviation \<open>\<phi>V_none \<equiv> sem_value ()\<close>
definition \<open>\<phi>V_pair x y = sem_value (dest_sem_value x, dest_sem_value y)\<close>
definition \<open>\<phi>V_fst x = map_sem_value fst x\<close>
definition \<open>\<phi>V_snd x = map_sem_value snd x\<close>
abbreviation \<open>\<phi>V_nil \<equiv> sem_value []\<close>
definition \<open>\<phi>V_cons h l = sem_value (dest_sem_value h # dest_sem_value l)\<close>
definition \<open>\<phi>V_hd l = sem_value (hd (dest_sem_value l))\<close>
definition \<open>\<phi>V_tl l = sem_value (tl (dest_sem_value l))\<close>

lemma \<phi>V_simps[simp]:
  \<open>\<phi>V_pair (\<phi>V_fst v) (\<phi>V_snd v) = v\<close>
  \<open>\<phi>V_fst (\<phi>V_pair u y) = u\<close>
  \<open>\<phi>V_snd (\<phi>V_pair x u) = u\<close>
  \<open>\<phi>V_cons (sem_value h) (sem_value l) = sem_value (h#l)\<close>
  \<open>\<phi>V_hd (\<phi>V_cons hv lv) = hv\<close>
  \<open>\<phi>V_tl (\<phi>V_cons hv lv) = lv\<close>
  unfolding \<phi>V_pair_def \<phi>V_fst_def \<phi>V_snd_def \<phi>V_cons_def \<phi>V_hd_def \<phi>V_tl_def
     apply (cases v, simp)
     apply (cases v, simp)
     apply (cases v, simp)
    apply simp apply simp apply simp .


subsubsection \<open>Monadic Formalization\<close>

datatype ('ret,'ex,'RES_N,'RES) state =
      Success \<open>'ret sem_value\<close> (resource: "('RES_N \<Rightarrow> 'RES)")
    | Exception \<open>'ex sem_value\<close> (resource: "('RES_N \<Rightarrow> 'RES)")
    | Invalid | PartialCorrect



hide_const(open) resource

text\<open> The basic state of the \<phi>-system virtual machine is represented by type \<open>('a::lrep) state\<close>.
  The valid state `Success` essentially has two major form, one without registers and another one with them,
      \<^item> \<open>StatOn (x1, x2, \<cdots>, xn, void)\<close>,
  where \<open>(x1, x2, \<cdots>, xn, void)\<close> represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term PartialCorrect} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term PartialCorrect} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>

declare state.split[split]

type_synonym ('ret,'ex,'RES_N,'RES) proc = "('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('ret,'ex,'RES_N,'RES) state set"
type_synonym ('arg,'ret,'ex,'RES_N,'RES) proc' = "'arg sem_value \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc"


definition bind :: "('a,'e,'RES_N,'RES) proc \<Rightarrow> ('a,'b,'e,'RES_N,'RES) proc' \<Rightarrow> ('b,'e,'RES_N,'RES) proc"  ("_ \<bind>/ _" [75,76] 75)
  where "bind f g = (\<lambda>res. \<Union>((\<lambda>y. case y of Success v x \<Rightarrow> g v x | Exception v x \<Rightarrow> {Exception v x}
                                       | Invalid \<Rightarrow> {Invalid} | PartialCorrect \<Rightarrow> {PartialCorrect}) ` f res))"

abbreviation bind' ("_ \<ggreater>/ _" [75,76] 75)
  where \<open>bind' f g \<equiv> (f \<bind> (\<lambda>_. g))\<close>

definition \<open>det_lift f x = {f x}\<close>
definition \<open>Return = det_lift o Success\<close>
definition Nondet :: \<open>('ret,'ex,'RES_N,'RES) proc \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc \<Rightarrow> ('ret,'ex,'RES_N,'RES) proc\<close>
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
  for f_nil :: \<open>(unit,'ex,'RES_N,'RES) proc\<close>
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