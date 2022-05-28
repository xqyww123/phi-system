(* KEEP IT SIMPLE AND STUPID *)

theory NuPrime \<comment> \<open>The Primary Theory of the \<nu>-System\<close>
  imports Main "HOL-Library.Word"
    "HOL-Library.Adhoc_Overloading"
    Fictional_Algebra
    "Virt_Datatype/Virtual_Datatype"
    Resource_Space
    NoeMisc
  keywords "value_model_space" :: thy_defn
    and "type_model_space" :: thy_defn
begin

text \<open>The fundamental theory for \<nu>-system\<close>

section Preliminary


named_theorems \<nu>elim "\<nu>-type elimination rules"
named_theorems \<nu>def \<open>primitive definitions used to unfold in proofs of primitive instructions.\<close>
  (* and \<nu>address_def \<open>primitive definitions for unfolding in proofs for address\<close> *)
  and \<nu>post_construct and \<nu>auto_destruct
named_theorems typing_expn "expansion theorems for abstractions" and lrep_exps and nu_exps

section\<open>Low representation for semantics\<close>

subsection \<open>Models\<close>

virtual_datatype std_ty =
  T_int :: nat
  T_pointer :: unit
  T_tup :: 'self
  T_array :: "'self \<times> nat"
  T_nil :: unit

(* datatype llty = T_int nat \<comment> \<open>int bits\<close> | T_pointer | T_tup llty
  | T_array llty nat | T_nil *)


datatype ('ty) segidx = Null | MSegment nat \<comment> \<open>nonce\<close> (layout_of: 'ty)
declare segidx.map_id0[simp]

datatype ('offset,'ty) memaddr = memaddr (segment_of: "'ty segidx") (offset_of: 'offset ) (infixl "|:" 60)
declare memaddr.sel[iff]


abbreviation shift_addr :: "('a::plus,'ty) memaddr \<Rightarrow> 'a \<Rightarrow> ('a,'ty) memaddr" (infixl "||+" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. x + delta) id addr"
lemma memaddr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>base ofs. P (base |: ofs))" by (metis memaddr.exhaust)
lemma memaddr_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>base ofs. P (base |: ofs))" by (metis memaddr.exhaust)

lemma mem_shift_shift[simp]: "a ||+ i ||+ j = a ||+ (i + j)" for i :: nat by (cases a) simp

virtual_datatype 'ty std_val :: nonsepable_semigroup =
  V_int :: \<open>nat \<times> nat\<close>
  V_pointer :: \<open>(nat, 'ty) memaddr\<close>
  V_record :: \<open>'self list\<close>
  V_array :: \<open>'self list\<close>
  V_void :: unit

type_synonym 'v opstack = "'v list"
type_synonym varname = nat

resource_space ('val::nonsepable_semigroup,'ty) std_res =
  R_mem :: \<open>((nat, 'ty) memaddr \<rightharpoonup> 'val) partial\<close>
  R_var :: \<open>(varname \<rightharpoonup> 'val) partial\<close>


locale std_sem =
  std_ty  where CONS_OF = TY_CONS_OF and TYPE'NAME = \<open>TYPE('TY_N)\<close> and TYPE'REP = \<open>TYPE('TY)\<close>
+ std_val where CONS_OF = VAL_CONS_OF and TYPE'ty = \<open>TYPE('TY)\<close>
    and TYPE'NAME = \<open>TYPE('VAL_N)\<close> and TYPE'REP = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ std_res where TYPE'val = \<open>TYPE('VAL)\<close> and TYPE'ty = \<open>TYPE('TY)\<close>
    and TYPE'NAME = \<open>TYPE('RES_N)\<close> and TYPE'REP = \<open>TYPE('RES::comm_monoid_mult)\<close>
  for TY_CONS_OF and VAL_CONS_OF
+ fixes TYPE'TY_N :: \<open>'TY_N itself\<close>
    and TYPE'TY :: \<open>'TY itself\<close>
    and TYPE'VAL_N :: \<open>'VAL_N itself\<close>
    and TYPE'VAL :: \<open>'VAL itself\<close>
    and TYPE'RES_N :: \<open>'RES_N itself\<close>
    and TYPE'RES :: \<open>'RES itself\<close>
begin

definition "fiction_mem I = Fiction (\<lambda>x. { 1<R_mem := y> |y. y \<in> \<I> I x})"
lemma fiction_mem_\<I>[simp]:
  "\<I> (fiction_mem I) = (\<lambda>x. { 1<R_mem := y> |y. y \<in> \<I> I x})"
  unfolding fiction_mem_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def)

definition "fiction_var I = Fiction (\<lambda>x. { 1<R_var := y> |y. y \<in> \<I> I x})"
lemma fiction_var_\<I>[simp]:
  "\<I> (fiction_var I) = (\<lambda>x. { 1<R_var := y> |y. y \<in> \<I> I x})"
  unfolding fiction_var_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def)


definition "share_mem = fiction_mem (fiction.partialwise (
              fiction.pointwise (fiction.optionwise fiction.share)))"
definition "exclusive_var = fiction_var fiction.it"

end


fiction_space (in std_sem) std_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> =
  mem :: share_mem
  var :: exclusive_var

locale std = std_fic
  where TYPE'TY_N = \<open>TYPE('TY_N)\<close>
    and TYPE'TY = \<open>TYPE('TY)\<close>
    and TYPE'VAL_N = \<open>TYPE('VAL_N)\<close>
    and TYPE'VAL = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
    and TYPE'RES_N = \<open>TYPE('RES_N)\<close>
    and TYPE'RES = \<open>TYPE('RES::comm_monoid_mult)\<close>
    and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
    and TYPE'REP = \<open>TYPE('FIC::comm_monoid_mult)\<close>
+ fixes TYPE'TY_N :: \<open>'TY_N itself\<close>
    and TYPE'TY :: \<open>'TY itself\<close>
    and TYPE'VAL_N :: \<open>'VAL_N itself\<close>
    and TYPE'VAL :: \<open>'VAL itself\<close>
    and TYPE'RES_N :: \<open>'RES_N itself\<close>
    and TYPE'RES :: \<open>'RES itself\<close>
    and TYPE'NAME :: \<open>'FIC_N itself\<close>
    and TYPE'REP :: \<open>'FIC::comm_monoid_mult itself\<close>




subsection \<open>Resource Algebra\<close>



resource_space 'val std_res =
  R_mem :: "nat memaddr \<Rightarrow> ('val :: trivial_validity) option"
  R_stack :: "'val list"

fiction_space 'val std_fic =
  F_mem_share :: "nat memaddr \<Rightarrow> ('val :: trivial_validity) owned"

locale std =
  std_typ where NAME_TYPE = "TYP_CONS_TYPE" and VALUE_TYPE = "TYP_REP_TYPE"
+ std_val where NAME_TYPE = "VAL_CONS_TYPE" and VALUE_TYPE = "VAL_REP_TYPE"
+ std_res where NAME_TYPE = "RES_CONS_TYPE" and VALUE_TYPE = "RES_REP_TYPE"
    and RES_project_'val_Nat_nat_NuPrime_memaddr_fun = RES_project_'val_Nat_nat_NuPrime_memaddr_fun
+ std_fic where NAME_TYPE = "FIC_CONS_TYPE" and VALUE_TYPE = "FIC_REP_TYPE"
    and FIC_project_'val_Resource_Algebra_owned_Nat_nat_NuPrime_memaddr_fun = FIC_project_'val_Resource_Algebra_owned_Nat_nat_NuPrime_memaddr_fun
for TYP_CONS_TYPE :: "'TYP_CONS itself"
and TYP_REP_TYPE  :: "'TYP_REP itself"
and VAL_CONS_TYPE :: "'VAL_CONS itself"
and VAL_REP_TYPE  :: "('VAL_REP::discrete_ura) itself"
and RES_CONS_TYPE :: "'RES_CONS itself"
and RES_REP_TYPE  :: "('RES_REP::discrete_ura) itself"
and RES_project_'val_Nat_nat_NuPrime_memaddr_fun :: "'RES_REP \<Rightarrow> nat memaddr \<Rightarrow> 'VAL_REP"
and FIC_CONS_TYPE :: "'FIC_CONS itself"
and FIC_REP_TYPE  :: "('FIC_REP::discrete_ura) itself"
and FIC_project_'val_Resource_Algebra_owned_Nat_nat_NuPrime_memaddr_fun :: "'FIC_REP \<Rightarrow> nat memaddr \<Rightarrow> 'VAL_REP owned"



subsection \<open>Memory & Heap\<close>

(*datatype resource_key = MemAddress "nat memaddr" | ChainDB_key nat

lemma resource_key_forall: "All P \<longleftrightarrow> (\<forall>addr. P (MemAddress addr)) \<and> (\<forall>n. P (ChainDB_key n))" by (metis resource_key.exhaust)
lemma resource_key_exists: "Ex P \<longleftrightarrow> (\<exists>addr. P (MemAddress addr)) \<or> (\<exists>n. P (ChainDB_key n))" by (metis resource_key.exhaust)
*)
context std begin
type_synonym logaddr = "nat memaddr"
type_synonym comp = "value list ex option \<times> mem \<times> unit"
end

term finite

definition AvailableSegments :: "mem \<Rightarrow> segidx set"
  where "AvailableSegments heap = {seg. \<forall>ofs. heap (MemAddress (seg |: ofs)) = None}"

definition Heap :: "mem \<Rightarrow> bool" where "Heap h \<longleftrightarrow> infinite (AvailableSegments h)"

lemma [intro]: "Heap h \<Longrightarrow> Heap (h(k := v))" proof -
  have "AvailableSegments h \<subseteq> {(case k of MemAddress (seg |: ofs) \<Rightarrow> seg)} \<union> (AvailableSegments (h(k := v)))"
    unfolding AvailableSegments_def by auto 
  then show "Heap h \<Longrightarrow> Heap (h(k := v))" 
    unfolding Heap_def using infinite_super by auto
qed

lemma Heap_subset: "h' \<subseteq>\<^sub>m h \<Longrightarrow> Heap h \<Longrightarrow> Heap h' "
  unfolding Heap_def subgoal premises prems proof -
  have "AvailableSegments h \<subseteq> AvailableSegments h'"
    unfolding AvailableSegments_def using prems(1)
    by (smt (verit, best) Collect_mono domIff map_le_def)
  then show ?thesis using prems(2) using finite_subset by blast
qed done

lemma Heap_map_add: "Heap (h1 ++ h2) \<Longrightarrow> Heap h2"
  using Heap_subset map_le_map_add by blast

lemma Heap_restrict[intro]: "Heap h \<Longrightarrow> Heap (h |` S)"
  by (metis domIff map_le_def restrict_map_def Heap_subset)







subsection \<open>State Model\<close>

datatype state = Success (dest_state: comp) | Fail | PartialCorrect
text\<open> The basic state of the \<nu>-system virtual machine is represented by type "('a::lrep) state"}.
  The valid state `Success` essentially has two major form, one without registers and another one with them,
      \<^item> "StatOn (x1, x2, \<cdots>, xn, void)",
  where "(x1, x2, \<cdots>, xn, void)" represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term PartialCorrect} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term PartialCorrect} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>

declare state.split[split]

type_synonym proc = "comp \<Rightarrow> state"

(* consts fun_table :: " fun_addr \<rightharpoonup> 'a \<longmapsto> 'b "
consts fun_addr_NULL :: fun_addr

specification (fun_table)
  fun_addr_NULL: "fun_table fun_addr_NULL = None" by auto *)




text \<open>The semantic framework follows a style of shallow embedding, where semantics for different type (e.g. integers, floats)
  are modelled by different Isabelle type. Model types are constrained by the base type class {\it lrep} and types representing
  objects that supports certain features are constrained by specific sub-classes which extend the base class {\it lrep} finally. \<close>


class lrep =  \<comment>\<open>The basic class for types modelling concrete objects\<close>
  fixes llty :: " 'a itself \<Rightarrow> llty "
  fixes deepize :: " 'a \<Rightarrow> value "
  fixes shallowize :: " value \<Rightarrow> 'a "
  assumes deepize_inj[simp]: " shallowize (deepize x) = x "

lemma [simp]: "shallowize o deepize = id" by fastforce

lemma deepize_inj2[simp]: "deepize a = deepize b \<longleftrightarrow> a = b"
  using deepize_inj by metis

abbreviation "map_deepmodel f x \<equiv> deepize (f (shallowize x))"

syntax "_LLTY_" :: "type \<Rightarrow> logic" ("LLTY'(_')")
translations  "LLTY('x)" == "CONST llty TYPE('x)"

class ceq =  \<comment> \<open>equality comparison\<close>
  fixes ceqable :: " heap \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    \<comment> \<open>Whether two values could be compared for equality. e.g. two INF cannot be compared; the dangling pointer also cannot\<close>
  fixes ceq :: " 'a \<Rightarrow> 'a \<Rightarrow> bool" \<comment> \<open>The equality of two values.
    It is only valid when the two values could be compared, i.e., the @{term ceqable} for them is true.\<close>
  assumes ceqable_sym[simp]: "ceqable h x y = ceqable h y x"
  assumes ceq_refl[intro]: "ceqable h x x \<Longrightarrow> ceq x x"
  assumes ceq_sym[simp]: "ceqable h x y \<Longrightarrow> ceq x y \<longleftrightarrow> ceq y x"
  assumes ceq_trans: "ceqable h x y \<Longrightarrow> ceqable h y z \<Longrightarrow> ceqable h x z
    \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z"


subsection \<open>The \<nu>-type\<close>

type_synonym ('a,'b) \<nu> = " 'b \<Rightarrow> 'a set "

subsubsection \<open>Definitions\<close>

definition \<nu>Type :: "'b \<Rightarrow> ('a,'b) \<nu> \<Rightarrow> 'a set" (infix "\<tycolon>" 17) where " (x \<tycolon> T) = (T x)"
definition Inhabited :: " 'a set \<Rightarrow> bool" where  "Inhabited S = (\<exists>p. p \<in> S)"

abbreviation InhabitNu :: " 'b \<Rightarrow> ('a,'b) \<nu> \<Rightarrow> bool" ("_ \<ratio> _" [18,18] 17)
  where  " (x \<ratio> T) \<equiv> Inhabited (x \<tycolon> T)"

lemma typing_inhabited: "p \<in> (x \<tycolon> T) \<Longrightarrow> x \<ratio> T" unfolding Inhabited_def \<nu>Type_def by blast

subsubsection \<open>Properties\<close>

definition \<nu>Zero :: "('a::{zero,lrep},'b) \<nu> \<Rightarrow> 'b \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Zero N x \<longleftrightarrow> 0 \<in> (x \<tycolon> N)"

definition \<nu>Equal :: "('a::{lrep,ceq}, 'b) \<nu> \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Equal N can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 heap.
    can_eq x1 x2 \<and> p1 \<in> (x1 \<tycolon> N) \<and> p2 \<in> (x2 \<tycolon> N) \<longrightarrow> ceqable heap p1 p2 \<and> (ceq p1 p2 = eq x1 x2))"


section\<open>Structures for construction\<close>

subsection \<open>Stack structure\<close>

instantiation prod :: (lrep,lrep) lrep begin
definition llty_prod :: "('a \<times> 'b) itself \<Rightarrow> llty" where "llty_prod _ = llty_fusion LLTY('a) LLTY('b)"
definition deepize_prod :: " 'a \<times> 'b \<Rightarrow> value " where
  "deepize_prod = (\<lambda>(a,b). DM_fusion (deepize a) (deepize b))"
definition shallowize_prod :: "value \<Rightarrow> 'a \<times> 'b" where
  "shallowize_prod x = (case x of DM_fusion a b \<Rightarrow> (shallowize a, shallowize b))"
instance apply standard
  subgoal for x by (cases x) (auto simp add: shallowize_prod_def deepize_prod_def) done
end


primrec is_stack :: "value \<Rightarrow> bool" where
  "is_stack (DM_fusion a b) \<longleftrightarrow> is_stack b"
| "is_stack DM_void \<longleftrightarrow> True"
| "is_stack (DM_int _ _) \<longleftrightarrow> False"
| "is_stack (DM_pointer _) \<longleftrightarrow> False"
| "is_stack (DM_record _) \<longleftrightarrow> False"
| "is_stack (DM_array _) \<longleftrightarrow> False"
(* | "is_stack (DM_fun_addr _) \<longleftrightarrow> False" *)

typedef stack = "UNIV :: value list set"
  morphisms values_of stack ..

setup_lifting type_definition_stack

declare values_of_inverse[simp] values_of_inject[simp]
lemmas stack_inverse[simp] = stack_inverse[simplified]
lemmas stack_inject[simp] = stack_inject[simplified]

hide_fact stack.stack_inject stack.stack_inverse

abbreviation stack_cat (infixr "@\<^sub>s\<^sub>k" 65) where "(a @\<^sub>s\<^sub>k b) \<equiv> stack (values_of a @ values_of b)"
abbreviation stack_cons (infixr "#\<^sub>s\<^sub>k" 65) where "(a #\<^sub>s\<^sub>k b) \<equiv> stack (a # values_of b)"

lemma [simp]:
  "values_of a = values_of b @ values_of c \<longleftrightarrow> a = b @\<^sub>s\<^sub>k c"
  by (metis stack_inverse values_of_inverse)


class stack = lrep +
  fixes stack_deepize :: " 'a \<Rightarrow> stack "
  fixes stack_shallowize :: " stack \<Rightarrow> 'a "
(*  assumes stack_is_stack[simp]: "is_stack (deepize x)" *)
  assumes stack_deepize_inj[simp]: "stack_shallowize (stack_deepize k) = k"

text \<open>The \<^class>\<open>stack\<close> is an artificial constraint.
  Though \<^class>\<open>stack\<close> is identical to \<^class>\<open>lrep\<close> in logic, most of types e.g. word, are only
  instantiated to \<^class>\<open>lrep\<close> but no \<^class>\<open>stack\<close> deliberately, and only prod and void are
  instantiated to stack by the instantiation (lrep,stack) :: stack and void::stack.
  By this deliberate constraints, once a type of class stack, it must a recursive pair
  ending with void.\<close>


lemma stack_deepize_inj[simp]:
  "stack_deepize k1 = stack_deepize k2 \<longleftrightarrow> k1 = k2"
  by (metis stack_deepize_inj)
  
instantiation prod :: (lrep,stack) stack begin
primrec stack_deepize_prod :: " 'a \<times> 'b \<Rightarrow> stack "
  where "stack_deepize_prod (a,b) = deepize a #\<^sub>s\<^sub>k stack_deepize b"
definition stack_shallowize_prod :: " stack \<Rightarrow> 'a \<times> 'b "
  where [simp]: "stack_shallowize_prod s = (case values_of s of (a#b) \<Rightarrow> (shallowize a, stack_shallowize (stack b)))"
instance by standard (simp_all add: pair_All)
end

instantiation "stack" :: stack begin

primrec value_to_list :: "value \<Rightarrow> value list" where
  "value_to_list DM_void = []" | "value_to_list (DM_fusion x l) =  x # (value_to_list l)"
primrec list_to_value :: "value list \<Rightarrow> value" where
  "list_to_value [] = DM_void" | "list_to_value (x # l) =  DM_fusion x (list_to_value l)"
lemma stack_bij_list:
  "value_to_list (list_to_value l) = l"
  by (induct l) simp_all

definition deepize_stack :: " stack \<Rightarrow> value " where [simp]: "deepize_stack s = list_to_value (values_of s)"
definition shallowize_stack :: " value \<Rightarrow> stack " where [simp]: "shallowize_stack v = stack (value_to_list v)"
definition stack_deepize_stack :: " stack \<Rightarrow> stack " where [simp]: "stack_deepize_stack x = x"
definition stack_shallowize_stack :: " stack \<Rightarrow> stack " where [simp]: "stack_shallowize_stack x = x"
instance by standard (simp_all add: stack_bij_list)
end


subsection \<open>The \<nu>-System VM and Procedure construction structures\<close>

type_synonym assn = "(heap \<times> stack) set" \<comment> \<open>assertion\<close>

subsubsection \<open>Types specifying states\<close>

definition StrictStateTy :: " (heap \<times> 'a::lrep) set \<Rightarrow> 'a state set" ("!\<S> _" [56] 55)
  where "!\<S> T = {s. case s of Success x \<Rightarrow> x \<in> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"
definition LooseStateTy :: " (heap \<times> 'a::lrep) set \<Rightarrow> 'a state set" ("\<S> _" [56] 55)
  where "\<S> T = {s. case s of Success x \<Rightarrow> x \<in> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma StrictStateTy_expn[iff,\<nu>def]: "Success x \<in> !\<S> T \<equiv> x \<in> T"  "\<not> (Fail \<in> !\<S> T)"  "\<not> (PartialCorrect \<in> !\<S> T)"
  and LooseStateTy_expn[iff,\<nu>def]: "Success x \<in> \<S> T \<equiv> x \<in> T"  "\<not> (Fail \<in> \<S> T)"  "(PartialCorrect \<in> \<S> T)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
lemma LooseStateTy_expn' : "x \<in> \<S> T \<longleftrightarrow> x = PartialCorrect \<or> (\<exists>x'. x = Success x' \<and> x' \<in> T)"
  by (cases x) simp_all

lemma StrictStateTy_elim[elim]: "s \<in> !\<S> T \<Longrightarrow> (\<And>x. s = Success x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma StrictStateTy_intro[intro]: " x \<in> T \<Longrightarrow> Success x \<in> !\<S> T" by simp
lemma LooseStateTy_E[elim]:
  "s \<in> \<S> T \<Longrightarrow> (\<And>x. s = Success x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma LooseStateTy_I[intro]:
  " x \<in> T \<Longrightarrow> Success x \<in> \<S> T" and [intro]: "PartialCorrect \<in> \<S> T" by simp_all
lemma LooseStateTy_upgrade: "s \<in> \<S> T \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T" by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> !\<S> T \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T) \<Longrightarrow> s \<in> \<S> T" by (cases s) auto

subsubsection \<open>Shallow model and Deep model\<close>

definition Deepize :: " 'a::lrep set \<Rightarrow> value set " where "Deepize S = deepize ` S"
definition Shallowize :: " value set \<Rightarrow> 'a::lrep set " where "Shallowize S = { p. deepize p \<in> S}"

lemma Shallowize_Deepize[simp]: "Shallowize (Deepize S) = S "
  unfolding Deepize_def Shallowize_def by (simp add: image_iff set_eq_iff)

definition Deepize' :: " (heap \<times> 'a::stack) set \<Rightarrow> assn " where "Deepize' S = apsnd stack_deepize ` S"
definition Shallowize' :: " assn \<Rightarrow> (heap \<times> 'a::stack) set " where "Shallowize' S = {(h,s). (h,stack_deepize s) \<in> S}"

lemma Deepize'_expn: "(h, s) \<in> Deepize' M \<longleftrightarrow> (\<exists>s'. stack_deepize s' = s \<and> (h, s') \<in> M)"
  unfolding Deepize'_def image_iff Bex_def by auto

lemma Shallowize'_expn[nu_exps]:
  "(h, s) \<in> Shallowize' M \<longleftrightarrow> (h, stack_deepize s) \<in> M"
  unfolding Shallowize'_def by simp

lemma Shallowize'_Deepize'[simp]: "Shallowize' (Deepize' S) = S "
  unfolding Deepize'_def Shallowize'_def by (simp add: image_iff pair_exists Bex_def set_eq_iff)

lemma Deepize'_Deepize'[simp]: "Deepize' S = S" for S :: "assn"
  unfolding set_eq_iff pair_forall Deepize'_expn by simp

lemma Deepize'_inj[simp]:
  "Deepize' A = Deepize' B \<longleftrightarrow> A = B"
  unfolding set_eq_iff Deepize'_expn pair_forall by force

subsubsection \<open>Stack Element and Heap Object\<close>

consts Ele :: " 'a set \<Rightarrow> assn " ("ELE _" [17] 16)

definition Val_Ele :: " 'a::lrep set \<Rightarrow> assn " ("VAL _" [17] 16) where
  "(VAL T) = { (Map.empty, stack [v]) | v. v \<in> deepize ` T } "

adhoc_overloading Ele Val_Ele

lemma [nu_exps]:
  "(h,s) \<in> (VAL V) \<longleftrightarrow> h = Map.empty \<and> (\<exists>v. s = stack [deepize v] \<and> v \<in> V)"
  unfolding Val_Ele_def by simp blast

lemma [elim!,\<nu>elim]: "Inhabited (VAL T) \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: pair_exists nu_exps)


definition Obj_Ele :: " heap set \<Rightarrow> assn " ("OBJ _" [17] 16) where
  "(OBJ T) = { (h, stack []) | h. h \<in> T } "

adhoc_overloading Ele Obj_Ele

lemma [nu_exps]: "(h, s) \<in> (OBJ T) \<longleftrightarrow> s = stack [] \<and> h \<in> T"
  unfolding Obj_Ele_def by simp

lemma [nu_exps]: "(h, s) \<in> Shallowize' (OBJ T) \<longleftrightarrow> s = stack [] \<and> h \<in> T"
  unfolding Obj_Ele_def Shallowize'_expn by simp

lemma [elim!,\<nu>elim]: "Inhabited (OBJ T) \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: pair_exists nu_exps)


subsubsection \<open>Separation\<close>

definition disjoint :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " (infixl "\<perpendicular>" 60) where "disjoint A B \<longleftrightarrow> (A \<inter> B = {})"
lemma disjoint_rewL: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<notin> B)" unfolding disjoint_def by auto
lemma disjoint_rewR: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> B \<longrightarrow> x \<notin> A)" unfolding disjoint_def by auto
lemma [elim]: "A \<perpendicular> B \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False) \<Longrightarrow> C) \<Longrightarrow> C" unfolding disjoint_def by auto

lemma disjoint_empty [iff]: "{} \<perpendicular> S"  "S \<perpendicular> {}" unfolding disjoint_def by auto

definition Separation :: "assn \<Rightarrow> assn \<Rightarrow> assn" ( "_/ \<heavy_asterisk> _" [13,14] 13)
  where "(T \<heavy_asterisk> U) = {(h,s). (\<exists>h1 h2 s1 s2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> s = s1 @\<^sub>s\<^sub>k s2 \<and> (h2,s2) \<in> T \<and> (h1,s1) \<in> U) }"

translations
  "x \<tycolon> T \<heavy_asterisk> U" \<rightleftharpoons> "CONST Ele (x \<tycolon> T) \<heavy_asterisk> U"
  "T \<heavy_asterisk> y \<tycolon> U" \<rightleftharpoons> "T \<heavy_asterisk> CONST Ele (y \<tycolon> U)"

lemma Separation_expn:
  "(h,s) \<in> (T \<heavy_asterisk> U) \<longleftrightarrow> (\<exists>h1 h2 s1 s2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> s = s1 @\<^sub>s\<^sub>k s2 \<and> (h2,s2) \<in> T \<and> (h1,s1) \<in> U)"
  unfolding Separation_def by simp

lemma Separation_expn_R:
  "(h,s) \<in> (T \<heavy_asterisk> U) \<longleftrightarrow> (\<exists>h1 h2 s1 s2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> s = s1 @\<^sub>s\<^sub>k s2 \<and> (h1,s2) \<in> T \<and> (h2,s1) \<in> U)"
  unfolding Separation_def
  by simp (metis disjoint_def disjoint_rewR map_add_comm) 

lemma Separation_expn_V[nu_exps]:
  "(h, stack (deepize v # r)) \<in> (R \<heavy_asterisk> VAL V) \<longleftrightarrow> ((h, stack r) \<in> R \<and> v \<in> V )"
  unfolding Separation_def Shallowize'_expn
  by (simp add: nu_exps) force

lemma Separation_expn_V':
  "(h, s) \<in> (R \<heavy_asterisk> VAL V) \<longleftrightarrow> (\<exists>v r. s = stack (deepize v # r) \<and> (h, stack r) \<in> R \<and> v \<in> V )"
  unfolding Separation_def Shallowize'_expn
  by (simp add: nu_exps) force

lemma Separation_expn_O[nu_exps]:
  "(h,s) \<in> (R \<heavy_asterisk> OBJ H) \<longleftrightarrow>
  (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> (h2,s) \<in> Shallowize' R \<and> h1 \<in> H )"
  unfolding Separation_def Shallowize'_expn
  by (simp add: nu_exps)

lemma Separation_expn_O_R:
  "(h,s) \<in> (R \<heavy_asterisk> OBJ H) \<longleftrightarrow>
  (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> (h1,s) \<in> Shallowize' R \<and> h2 \<in> H )"
  unfolding Separation_def Shallowize'_expn
  by (simp add: nu_exps) (metis disjoint_def disjoint_rewR map_add_comm)

lemma [elim!,\<nu>elim]: "Inhabited (T \<heavy_asterisk> U) \<Longrightarrow> (Inhabited T \<Longrightarrow> Inhabited U \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: pair_exists nu_exps Separation_expn) blast


lemma Separation_assoc[simp]: "(A \<heavy_asterisk> (B \<heavy_asterisk> C)) = (A \<heavy_asterisk> B \<heavy_asterisk> C)"
  unfolding Separation_def set_eq_iff pair_forall
  apply auto subgoal for h2 s2 h1a h2a s1a s2a
    apply (rule exI [where x = "h1a"], rule exI [where x = "h2a ++ h2"],
          simp add: disjoint_def inf_sup_distrib1 inf_sup_distrib2)
    apply (rule exI [of _ s1a], rule exI [of _ "s2a @\<^sub>s\<^sub>k s2"], simp)
    apply blast done
  subgoal for h1 s1 h1a h2a s1a s2a
    apply (rule exI [where x = "h1 ++ h1a"], rule exI [where x = "h2a"],
          simp add: disjoint_def inf_sup_distrib1 inf_sup_distrib2)
    apply (rule exI [of _ "s1 @\<^sub>s\<^sub>k s1a"], simp, blast)
    done
  done

lemma Separation_comm:
  " (OBJ A \<heavy_asterisk> B) = (B \<heavy_asterisk> OBJ A) "
  " (A' \<heavy_asterisk> OBJ B') = (OBJ B' \<heavy_asterisk> A') "
  unfolding Separation_def set_eq_iff pair_forall
  by (simp_all add: disjoint_def nu_exps) (blast dest: map_add_comm)+

lemma shallowize_ex: "(\<exists>x::('c::lrep). P x) \<longleftrightarrow> (\<exists>x. P (shallowize x))"
  using deepize_inj by metis
lemma shallowize_ex': "TERM TYPE('c) \<Longrightarrow> (\<exists>x::('c::lrep). P x) \<longleftrightarrow> (\<exists>x. P (shallowize x))"
  using shallowize_ex .

lemma shallowize_all: "(\<forall>x::('c::lrep). P x) \<longleftrightarrow> (\<forall>x. P (shallowize x))"
  using deepize_inj by metis
lemma shallowize_all': "TERM TYPE('c) \<Longrightarrow> (\<forall>x::('c::lrep). P x) \<longleftrightarrow> (\<forall>x. P (shallowize x))"
  using shallowize_all .


lemma Separation_E[elim]:
  "(h,s) \<in> (T \<heavy_asterisk> U) \<Longrightarrow> (\<And>h1 h2 s1 s2. h = h1 ++ h2 \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> s = s1 @\<^sub>s\<^sub>k s2
      \<Longrightarrow> (h2,s2) \<in> T \<Longrightarrow> (h1,s1) \<in> U \<Longrightarrow> C) \<Longrightarrow> C "
  unfolding Separation_expn by simp blast

lemma Separation_I[intro]:
  "(h2,s2) \<in> T \<Longrightarrow> (h1,s1) \<in> U \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> s = s1 @\<^sub>s\<^sub>k s2 \<Longrightarrow> (h1 ++ h2, s) \<in> (T \<heavy_asterisk> U)"
  unfolding Separation_expn by simp blast

subsubsection \<open>Set style Heap predication\<close>

definition Heap' :: "(heap \<times> 's::stack) set \<Rightarrow> (heap \<times> 's::stack) set"
  where "Heap' T = {(h,s). Heap h \<and> (h,s) \<in> T}"

lemma Heap'_expn[simp,\<nu>def]: "(h,s) \<in> Heap' T \<longleftrightarrow> Heap h \<and> (h,s) \<in> T"
  unfolding Heap'_def by simp

subsubsection \<open>\<nu>-Procedure\<close>

text \<open>An assertion identical to Hoare triple, in the language of \<nu>-type. 
  \<^const>\<open>Heap'\<close> and \<^const>\<open>Shallowize'\<close> are auxiliary usage.\<close>

definition Procedure :: "('c::stack \<longmapsto> 'd::stack) \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> bool" ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ \<blangle>(2 _/  \<longmapsto>  _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]:"Procedure f T U \<longleftrightarrow>
      (\<forall>a M::assn. a \<in> Heap' (Shallowize' (M \<heavy_asterisk> T)) \<longrightarrow> f a \<in> \<S> Heap' (Shallowize' (M \<heavy_asterisk> U)))"


translations
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> a \<tycolon> A \<longmapsto> B \<brangle>" \<rightleftharpoons> "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> CONST Ele (a \<tycolon> A) \<longmapsto> B \<brangle>"
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> b \<tycolon> B \<brangle>" \<rightleftharpoons> "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> CONST Ele (b \<tycolon> B) \<brangle>"

definition Map :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set " where "Map A B = {f. \<forall>a. a \<in> A \<longrightarrow> f a \<in> B }"
definition Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<blangle>(2 _/ \<longmapsto> _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle> \<equiv> \<forall>a. a \<in> T \<longrightarrow> f a \<in> U"


subsection \<open>Primitive operations and instructions required in the system\<close>

subsubsection \<open>Elementary instructions\<close>

definition bind :: " ('a::lrep) state \<Rightarrow> ( 'a \<longmapsto> 'b) \<Rightarrow> ('b::lrep) state " \<comment>\<open>monadic bind\<close>
  where "bind s f = (case s of Success x \<Rightarrow> f x | Fail \<Rightarrow> Fail | PartialCorrect \<Rightarrow> PartialCorrect)"
definition instr_comp :: "(('a::lrep) \<longmapsto> ('b::lrep)) \<Rightarrow> ( 'b \<longmapsto> ('c::lrep)) \<Rightarrow> 'a \<longmapsto> 'c"  ("_ \<then>/ _" [75,76] 75) 
  where "instr_comp f g s = bind (f s) g"
definition nop :: " ('a::lrep) \<longmapsto> 'a" where "nop = Success" \<comment>\<open>the instruction `no-operation`\<close>

lemma nop_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> T \<longmapsto> T \<brangle>" unfolding nop_def Procedure_def by auto
lemma instr_comp[intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> B \<longmapsto> C \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<then> g) \<blangle> A \<longmapsto> C \<brangle>"
  unfolding instr_comp_def Procedure_def bind_def by (auto 0 4)


subsection \<open>Top-level Construction Structures\<close>

subsubsection \<open>Construction Context & Code block\<close>

definition CurrentConstruction :: " ('a::stack) state \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> bool "
    ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,11] 10)
  where "CurrentConstruction s R S \<longleftrightarrow> s \<in> !\<S> Heap' (Shallowize' (R \<heavy_asterisk> S))"
definition PendingConstruction :: " (('a::stack) \<longmapsto> ('b::stack)) \<Rightarrow> 'a state \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> bool "
    ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,1000,5] 4)
  where "PendingConstruction f s R S \<longleftrightarrow> bind s f \<in> \<S> Heap' (Shallowize' (R \<heavy_asterisk> S))"
translations
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> T)" \<rightleftharpoons> "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ELE x \<tycolon> T"
  "CONST PendingConstruction f s H (x \<tycolon> T)" \<rightleftharpoons> "CONST PendingConstruction f s H (ELE x \<tycolon> T)"

lemma CurrentConstruction_D: "CurrentConstruction s H T \<Longrightarrow> Inhabited T"
  unfolding CurrentConstruction_def Inhabited_def by (cases s) (auto 0 4 simp add: Shallowize'_expn)


definition CodeBlock :: " ('a::lrep) state \<Rightarrow> ('b::lrep) state => ('b \<longmapsto> 'a) \<Rightarrow> bool" where
  CodeBlock_def: "CodeBlock stat arg prog \<longleftrightarrow> (bind arg prog = stat \<and> stat \<noteq> PartialCorrect)"
syntax "_codeblock_exp_" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> bool"  ("(2\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _/  \<^bold>a\<^bold>s '\<open>_'\<close>/ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>)" [100,0,0] 3)
syntax "_codeblock_" :: "idt \<Rightarrow> logic \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>" [100,0] 3)


section \<open>Rules for the construction\<close>

lemma frame: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> M \<heavy_asterisk> A \<longmapsto> M \<heavy_asterisk> B \<brangle>"
  unfolding Procedure_def by simp

lemma apply_proc: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def by (auto 0 5)

lemma accept_proc: "\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> CodeBlock s' s f \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  for s' :: "('b::stack) state"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def
  by (simp add: LooseStateTy_upgrade)

lemma reassemble_proc_0:
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g nop \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def nop_def bind_def by (cases s) simp+

lemma reassemble_proc:
  "(\<And>s'. CodeBlock s' s f \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s' [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<then> g) \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def bind_def instr_comp_def
  by force

lemma reassemble_proc_final:
  "(\<And>s H. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> S \<longmapsto> T \<brangle>"
  unfolding CurrentConstruction_def PendingConstruction_def Procedure_def bind_def pair_All
  by (metis StrictStateTy_intro state.simps(8))

lemma rename_proc: "f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U \<longmapsto> \<R> \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> \<R> \<brangle>" by fast

end
