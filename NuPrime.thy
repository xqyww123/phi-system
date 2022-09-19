(* KEEP IT SIMPLE AND STUPID *)

theory NuPrime \<comment> \<open>The Primary Theory of the \<phi>-System\<close>
  imports Main
    NoePreliminary
    Fictional_Algebra
    "Virt_Datatype/Virtual_Datatype"
    BI_for_Phi
  abbrevs "<:>" = "\<Ztypecolon>"
    and "<throws>" = "\<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s"
    and "<proc>" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
    and "<view>" = "\<^bold>v\<^bold>i\<^bold>e\<^bold>w"
    and "<with>" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
begin

chapter \<open>Semantics & Specification Framework --- Base of the Programming Language\<close>

section \<open>Semantic Framework\<close>

subsection \<open>Semantic Models\<close>

subsubsection \<open>Global Parameter\<close>

consts addrspace_bits :: "nat" \<comment> \<open>The bit length of the memory address space, in unit of bits\<close>
specification (addrspace_bits) addrspace_bits_L0: "0 < addrspace_bits" by auto


subsubsection \<open>Type\<close>

virtual_datatype \<phi>empty_ty

subsubsection \<open>Value\<close>

virtual_datatype 'TY \<phi>empty_val :: "nonsepable_semigroup"

print_locale \<phi>empty_val

subsubsection \<open>Resource\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) \<phi>empty_res

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

subsection \<open>Empty Semantics\<close>

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

subsubsection \<open>Empty Fiction\<close>

locale \<phi>fiction =
  \<phi>resource_sem Resource_Validator
+ fictional_space INTERPRET
for Resource_Validator :: "'RES_N \<Rightarrow> 'RES::sep_algebra set"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra, 'RES_N \<Rightarrow> 'RES::sep_algebra) fiction"
begin

definition "INTERP_RES fic \<equiv> Valid_Resource \<inter> S_Assert (Fic_Space fic) \<inter> \<I> INTERP fic"

definition INTERP_COM :: \<open>('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('RES_N \<Rightarrow> 'RES) set\<close>
  where "INTERP_COM T = { res. \<exists>fic. fic \<in> T \<and> res \<in> INTERP_RES fic }"

lemma INTERP_COM[\<phi>expns]:
  \<open>res \<in> INTERP_COM T \<longleftrightarrow> (\<exists>fic. fic \<in> T \<and> res \<in> INTERP_RES fic)\<close>
  unfolding INTERP_COM_def by simp

lemma INTERP_COM_subset[intro, simp]: \<open>A \<subseteq> B \<Longrightarrow> INTERP_COM A \<subseteq> INTERP_COM B\<close>
  unfolding INTERP_COM_def subset_iff by simp blast

lemma INTERP_COM_plus[iff]:
  \<open>INTERP_COM (A + B) = INTERP_COM A + INTERP_COM B\<close>
  unfolding INTERP_COM_def plus_set_def by simp blast

lemma INTERP_COM_empty[intro, simp]:
  \<open>S = {} \<Longrightarrow> INTERP_COM S = {}\<close>
  unfolding INTERP_COM_def set_eq_iff by simp

lemma  INTERP_COM_subj[\<phi>expns]:
  \<open> INTERP_COM (S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) = (INTERP_COM S \<^bold>s\<^bold>u\<^bold>b\<^bold>j P) \<close>
  unfolding INTERP_COM_def by (simp add: \<phi>expns set_eq_iff, blast)

lemma  INTERP_COM_ex[\<phi>expns]:
  \<open> INTERP_COM (ExSet S) = (\<exists>\<^sup>s x. INTERP_COM (S x)) \<close>
  unfolding INTERP_COM_def by (simp add: \<phi>expns set_eq_iff, blast)


lemma INTERP_COM_0[simp]:
  \<open>INTERP_COM 0 = 0\<close>
  \<open>INTERP_COM {} = {}\<close>
  unfolding INTERP_COM_def zero_set_def by simp+

lemma INTERP_mono:
  \<open> Fic_Space fic
\<Longrightarrow> Fic_Space x
\<Longrightarrow> dom1 res \<inter> dom1 p = {}
\<Longrightarrow> dom1 fic \<inter> dom1 x = {}
\<Longrightarrow> res \<in> \<I> INTERP fic
\<Longrightarrow> p \<in> \<I> INTERP x
\<Longrightarrow> fic ## x
\<Longrightarrow> res * p \<in> \<I> INTERP (fic * x) \<and> res ## p\<close>
  unfolding INTERP_def Fic_Space_def
  apply (simp add: dom1_sep_mult_disjoint times_fun prod.union_disjoint
                   disjoint_dom1_eq_1[of fic x])
  by (meson dom1_disjoint_sep_disj times_set_I)

end

subsubsection \<open>Empty Settings\<close>

locale \<phi>empty =
  \<phi>fiction Resource_Validator INTERPRET
+ \<phi>empty_sem where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                               \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                               \<times> ('RES_N \<Rightarrow> 'RES::sep_algebra))\<close>
             and Resource_Validator = Resource_Validator
for Resource_Validator :: "'RES_N \<Rightarrow> 'RES::sep_algebra set"
and INTERPRET :: "'FIC_N \<Rightarrow> ('FIC::sep_algebra, 'RES_N \<Rightarrow> 'RES::sep_algebra) fiction"
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

subsection \<open>Explicit Annotation of Semantic Arguments and Returns\<close>

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


subsection \<open>Monadic Formalization\<close>

datatype ('ret,'ex,'RES_N,'RES) state =
      Success \<open>'ret sem_value\<close> (resource: "('RES_N \<Rightarrow> 'RES)")
    | Exception \<open>'ex sem_value\<close> (resource: "('RES_N \<Rightarrow> 'RES)")
    | Invalid | PartialCorrect



hide_const(open) resource

text\<open> The basic state of the \<phi>-system virtual machine is represented by type "('a::lrep) state"}.
  The valid state `Success` essentially has two major form, one without registers and another one with them,
      \<^item> "StatOn (x1, x2, \<cdots>, xn, void)",
  where "(x1, x2, \<cdots>, xn, void)" represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
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


section \<open>Specification Framework\<close>

type_synonym ('RES_N,'RES) assn = "('RES_N \<Rightarrow> 'RES) set" \<comment> \<open>assertion\<close>

subsection \<open>Preliminary\<close>

subsubsection \<open>Predicates for Total Correctness & Partial Correctness\<close>

context \<phi>resource_sem begin

definition StrictStateTy :: "('ret sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('ex  sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('ret,'ex,'RES_N,'RES) state set" ("!\<S>")
  where "!\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val | Exception val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"
definition LooseStateTy  :: "('ret sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('ex  sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('ret,'ex,'RES_N,'RES) state set" ("\<S>")
  where  "\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val | Exception val x \<Rightarrow> x \<in> E val
                              | Invalid \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma StrictStateTy_expn[iff,\<phi>def]:
        "Success vs x \<in> !\<S> T E \<equiv> x \<in> T vs" "Exception v x \<in> !\<S> T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> !\<S> T E)"  "\<not> (PartialCorrect \<in> !\<S> T E)"
  and LooseStateTy_expn[iff,\<phi>def]:
        "Success vs x \<in> \<S> T E \<equiv> x \<in> T vs" "Exception v x \<in> \<S> T E \<equiv> x \<in> E v"
        "\<not> (Invalid \<in> \<S> T E)"  "(PartialCorrect \<in> \<S> T E)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
lemma LooseStateTy_expn' :
    "x \<in> \<S> T E \<longleftrightarrow> x = PartialCorrect \<or> (\<exists>x' v. x = Success v x' \<and> x' \<in> T v) \<or> (\<exists>x' v. x = Exception v x' \<and> x' \<in> E v)"
  by (cases x) simp_all

lemma StrictStateTy_elim[elim]:
    "s \<in> !\<S> T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Exception v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> C" by (cases s) auto
lemma StrictStateTy_intro[intro]:
    " x \<in> T v \<Longrightarrow> Success v x \<in> !\<S> T E"
    " x \<in> E v \<Longrightarrow> Exception v x \<in> !\<S> T E"
  by simp_all
lemma LooseStateTy_E[elim]:
    "s \<in> \<S> T E
\<Longrightarrow> (\<And>x v. s = Success v x \<Longrightarrow> x \<in> T v \<Longrightarrow> C)
\<Longrightarrow> (\<And>x v. s = Exception v x \<Longrightarrow> x \<in> E v \<Longrightarrow> C)
\<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C)
\<Longrightarrow> C"
  by (cases s) auto
lemma LooseStateTy_I[intro]:
  "x \<in> T v \<Longrightarrow> Success v x \<in> \<S> T E"
  "x \<in> E v \<Longrightarrow> Exception v x \<in> \<S> T E"
  "PartialCorrect \<in> \<S> T E"
  by simp_all

lemma LooseStateTy_upgrade:
  "s \<in> \<S> T E \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T E"
  by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> !\<S> T E \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T E) \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto

lemma StrictStateTy_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> !\<S> A E \<subseteq> !\<S> A' E'\<close>
  unfolding subset_iff StrictStateTy_def by simp
lemma StrictStateTy_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> !\<S> A E \<Longrightarrow> s \<in> !\<S> A' E'\<close>
  unfolding StrictStateTy_def by (cases s; simp)

lemma LooseStateTy_subset:
  \<open>(\<And>v. A v \<subseteq> A' v) \<Longrightarrow> (\<And>v. E v \<subseteq> E' v) \<Longrightarrow> \<S> A E \<subseteq> \<S> A' E'\<close>
  unfolding subset_iff LooseStateTy_def by simp
lemma LooseStateTy_subset'[intro]:
  \<open>(\<And>v. \<forall>s. s \<in> A v \<longrightarrow> s \<in> A' v) \<Longrightarrow> (\<And>v. \<forall>s. s \<in> E v \<longrightarrow> s \<in> E' v) \<Longrightarrow> s \<in> \<S> A E \<Longrightarrow> s \<in> \<S> A' E'\<close>
  unfolding LooseStateTy_def by (cases s; simp)


lemma LooseStateTy_plus[iff]:
(*  \<open>\<S> (A + B) E   = \<S> A E + \<S> B E\<close> *)
  \<open>\<S> X (\<lambda>v. EA v + EB v) = \<S> X EA + \<S> X EB\<close>
  unfolding set_eq_iff LooseStateTy_def by simp_all
lemma StrictStateTy_plus[iff]:
(*  \<open>!\<S> (A + B) E   = !\<S> A E  + !\<S> B E\<close> *)
  \<open>!\<S> X (\<lambda>v. EA v + EB v) = !\<S> X EA + !\<S> X EB\<close>
  unfolding set_eq_iff StrictStateTy_def by simp_all

end

abbreviation (in \<phi>fiction) \<open>Void \<equiv> (1::('FIC_N,'FIC) assn)\<close>


subsection \<open>Assertion\<close>

context \<phi>fiction begin
(* definition Fiction_Spec :: \<open>('FIC_N, 'FIC) assn \<Rightarrow> ('ret,'RES_N,'RES) proc \<Rightarrow> ('ret sem_value \<Rightarrow> ('FIC_N,'FIC) assn) \<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> bool\<close>
  where \<open>Fiction_Spec P C Q E \<longleftrightarrow>
    (\<forall>com. com \<in> INTERP_COM P \<longrightarrow> C com \<in> \<S> (\<lambda>v. INTERP_COM (Q v)) (INTERP_COM E))\<close> *)

definition \<phi>Procedure :: "('ret,'ex,'RES_N,'RES) proc
                        \<Rightarrow> ('FIC_N,'FIC) assn
                        \<Rightarrow> ('ret sem_value \<Rightarrow> ('FIC_N,'FIC) assn)
                        \<Rightarrow> ('ex  sem_value \<Rightarrow> ('FIC_N,'FIC) assn)
                        \<Rightarrow> bool"
    ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _ \<rbrace>))" [101,2,2,2] 100)
  where [\<phi>def]:"\<phi>Procedure f T U E \<longleftrightarrow>
    (\<forall>comp R. comp \<in> INTERP_COM (R * T) \<longrightarrow> f comp \<subseteq> \<S> (\<lambda>v. INTERP_COM (R * U v)) (\<lambda>v. INTERP_COM (R * E v)))"

abbreviation \<phi>Procedure_no_exception ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<rbrace>))" [101,2,2] 100)
  where \<open>\<phi>Procedure_no_exception f T U \<equiv> \<phi>Procedure f T U 0\<close>

lemma \<phi>Procedure_alt:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> T \<longmapsto> U \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<longleftrightarrow> (\<forall>comp r. comp \<in> INTERP_COM ({r} * T) \<longrightarrow> f comp \<subseteq> \<S> (\<lambda>v. INTERP_COM ({r} * U v)) (\<lambda>v. INTERP_COM ({r} * E v)))\<close>
  apply rule
   apply ((unfold \<phi>Procedure_def)[1], blast)
  unfolding \<phi>Procedure_def INTERP_COM subset_iff
  apply (clarsimp simp add: times_set_def)
  subgoal for comp R s r p
    apply (cases \<open>s\<close>; simp add: \<phi>expns INTERP_COM_def)
    apply fastforce
    subgoal premises prems for e
      apply (insert prems(1)[THEN spec[where x=comp], THEN spec[where x=r], simplified prems, simplified])
      using prems(2) prems(3) prems(4) prems(5) prems(6) by blast
    subgoal premises prems
      apply (insert prems(1)[THEN spec[where x=comp], THEN spec[where x=r], simplified prems, simplified])
      using prems(2) prems(4) prems(5) prems(6) by blast . .

lemmas \<phi>Procedure_I = \<phi>Procedure_alt[THEN iffD2]


subsection \<open>View Shift\<close>

definition View_Shift
    :: "('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> bool \<Rightarrow> bool" ("(2\<^bold>v\<^bold>i\<^bold>e\<^bold>w _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [13,13,13] 12)
  where "View_Shift T U P \<longleftrightarrow> (\<forall>x R. x \<in> INTERP_COM (R * T) \<longrightarrow> x \<in> INTERP_COM (R * U) \<and> P)"

abbreviation Simple_View_Shift
    :: "('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> bool" ("(2\<^bold>v\<^bold>i\<^bold>e\<^bold>w _/ \<longmapsto> _)"  [13,13] 12)
  where \<open>Simple_View_Shift T U \<equiv> View_Shift T U True\<close>



subsection \<open>Essential Hoare Rules\<close>

lemma \<phi>SKIP[simp,intro!]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c det_lift (Success v) \<lbrace> T v \<longmapsto> T \<rbrace>"
  unfolding \<phi>Procedure_def det_lift_def by clarsimp

lemma \<phi>SEQ:
   "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> (\<And>vs. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g vs \<lbrace> B vs \<longmapsto> C \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<bind> g) \<lbrace> A \<longmapsto> C \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>"
  unfolding \<phi>Procedure_def bind_def apply (clarsimp simp add: subset_iff)
  subgoal for comp R x s
    apply (cases s; clarsimp; cases x; clarsimp; blast) . .

lemma \<phi>frame:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s \<lambda>ex. R * E ex \<rbrace>"
  unfolding \<phi>Procedure_def subset_iff
  apply clarify subgoal premises prems for comp R' s
    using prems(1)[THEN spec[where x=comp], THEN spec[where x=\<open>R' * R\<close>],
          simplified mult.assoc, THEN mp, OF prems(2)] prems(3) by blast .

lemma \<phi>frame0:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<rbrace>"
  using \<phi>frame[where E=0, simplified, folded zero_fun_def] .

lemma \<phi>frame_view:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w R * A \<longmapsto> R * B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc)

lemma \<phi>frame_view_right:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A * R \<longmapsto> B * R \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding View_Shift_def
  by (metis (no_types, lifting) mult.assoc mult.commute)

lemma \<phi>view_refl:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w X \<longmapsto> X \<close>
  unfolding View_Shift_def by blast

lemma \<phi>view_trans:
  \<open> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2\<close>
  unfolding View_Shift_def by blast

lemma \<phi>view_shift_by_implication:
  \<open> A \<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>e\<^bold>s B \<^bold>a\<^bold>n\<^bold>d P
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P\<close>
  unfolding View_Shift_def Imply_def
  by (metis INTERP_COM set_mult_expn)

lemma \<phi>CONSEQ:
   "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A  \<longmapsto> B  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  \<rbrace>
\<Longrightarrow> \<^bold>v\<^bold>i\<^bold>e\<^bold>w A' \<longmapsto> A \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any1
\<Longrightarrow> (\<And>ret. \<^bold>v\<^bold>i\<^bold>e\<^bold>w B ret \<longmapsto> B' ret \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any2)
\<Longrightarrow> (\<And>ex.  \<^bold>v\<^bold>i\<^bold>e\<^bold>w E ex  \<longmapsto> E' ex  \<^bold>w\<^bold>i\<^bold>t\<^bold>h Any3)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A' \<longmapsto> B' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>"
  unfolding \<phi>Procedure_def View_Shift_def subset_iff
  apply clarsimp
  by (smt (verit, del_insts) LooseStateTy_expn')
  
end

parse_translation \<open> let
  val typ_tag = Const (\<^type_syntax>\<open>proc\<close>, dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
        $ Free ("'VAL", dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
        $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT)
  fun do_tag_E E = Const (\<^syntax_const>\<open>_constrain\<close>, dummyT) $ E $ typ_tag
  fun tag_E (E as Const (\<^syntax_const>\<open>_constrain\<close>, _) $ Free _ $ _) = do_tag_E E
    | tag_E (E as Const (\<^syntax_const>\<open>_constrain\<close>, _) $ _ $ _) = E
    | tag_E E = do_tag_E E
in [
  ("\<^const>local.\<phi>Procedure", (fn ctxt => fn [f,T,U,E] =>
    (Const("\<^const>local.\<phi>Procedure", dummyT) $ tag_E f $ T $ U $ E))),
  ("\<^const>local.\<phi>Procedure_no_exception", (fn ctxt => fn [f,T,U] =>
    (Const("\<^const>local.\<phi>Procedure_no_exception", dummyT) $ tag_E f $ T $ U)))
] end\<close>

end
