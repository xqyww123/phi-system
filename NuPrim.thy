(* KEEP IT SIMPLE AND STUPID *)

theory NuPrim
  imports Main
  abbrevs "is" = "\<B_i>\<B_s>"
      and "register" = "\<B_r>\<B_e>\<B_g>\<B_i>\<B_s>\<B_t>\<B_e>\<B_r>"
      and "in" = "\<B_i>\<B_n>"
      and "with" = "\<B_w>\<B_i>\<B_t>\<B_h>"
      and "auxiliary_facts" = "\<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>"
      and "auxfacts" = "\<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>"
begin

text \<open>The fundamental theory for \<nu>-system\<close>

section Preliminary

declare [[quick_and_dirty = true]]
bundle show_more1 = [[show_hyps = true, show_types = true, show_sorts = true]]
bundle show_more = [[show_hyps = true, show_types = true]]

named_theorems abst_expn "expansion theorems for abstractions"

datatype zint = Gz | Gi int
text\<open> Type @{typ zint} is used to represent ownership. @{term "Gi i"} represents
  $2^{-i}$ part of the ownership, and @{term "Gi 0"} is the total. @{term Gz} represents
  some ownership of unknown quantity. Any value of @{type zint} represents
  some part of (or total) ownership. The empty ownership is represented
  by further structure like @{typ "zint option"} as @{term None}\<close>

instantiation zint :: comm_monoid_add begin

definition zero_zint_def[simp]: "0 = Gi 0"
definition plus_zint_def: "a + b = (case (a,b) of
    (Gi n, Gi m) \<Rightarrow> Gi (n + m)  | _ \<Rightarrow> Gz)"

lemma plus_zint_simps1[simp]:  "Gi n + Gi m = Gi (n + m)"  by (simp add: plus_zint_def)
lemma plus_zint_simps2[simp]:  "Gz + x = Gz" by (simp add: plus_zint_def)
lemma plus_zint_simps3[simp]:  "x + Gz = Gz" by (cases x,auto simp add: plus_zint_def)

instance by standard ((simp add: plus_zint_def split: zint.splits)+)
end  

definition K_def[simp]: "K a b = a"
lemma K_intro[intro]: "(\<forall>x y. f x y = x) \<Longrightarrow> f = K" by (simp add: ext)

section\<open>Fundamentals for low level representation\<close>

datatype layout = la_i nat | la_p nat | la_s layout
  | la_a layout nat | la_z | la_C layout layout

class llty = fixes layout :: "'a itself \<Rightarrow> layout"
  \<comment>\<open>The class for basic low level types\<close>

text \<open>The ability for memory allocation\<close>
class zero_llty = llty +
  fixes lty_zero :: "'a"

text \<open>The ability for equality comparison\<close>
class ceq_llty = llty +
  fixes ceqable :: "('a * 'a) \<Rightarrow> bool"
  fixes ceq :: "('a * 'a) \<Rightarrow> bool"
  assumes ceqable_sym[ac_simps]: "ceqable (x,y) = ceqable (y,x)"
  assumes ceq_refl[simp]: "ceqable (x,x) \<Longrightarrow> ceq (x,x)"
  assumes ceq_sym: "ceqable (x,y) \<Longrightarrow> ceq (x,y) \<longleftrightarrow> ceq (y,x)"
  assumes ceq_trans: "ceqable (x,y) \<Longrightarrow> ceqable (y,z) \<Longrightarrow> ceqable (x,z)
    \<Longrightarrow> ceq(x,y) \<Longrightarrow> ceq (y,z) \<Longrightarrow> ceq (x,z)"

class sharable_llty = llty + 
  fixes revert :: "'a * 'a \<Rightarrow> bool"
    and sharable :: "'a \<Rightarrow> bool"
    and share :: "'a \<Rightarrow> zint \<Rightarrow> 'a"
    and dpriv :: "'a \<Rightarrow> 'a"
  assumes revert_refl[simp]: "revert (x,x)"
  assumes revert_sym[ac_simps]: "revert (x,y) \<longleftrightarrow> revert (y,x)"
  assumes revert_trans: "revert (x,y) \<Longrightarrow> revert (y,z) \<Longrightarrow> revert (x,z)"
  assumes share_id[simp]: "share x (Gi 0) = x"
  assumes share_assoc[simp]: "share (share x a) b = share x (a + b)"

class masharable_llty = sharable_llty +
  assumes marsharable_sha[simp]: "sharable x = True"
  assumes marsharable_dp[simp]: "dpriv = id"
  assumes marsharable_sh[simp]: "share = K"
  assumes marsharable_rt[simp]: "revert xy = True"  

datatype 'a state = StatOn 'a | STrap | SNeg

datatype ('a,'b) nu = Nu "('a::llty) * 'b \<Rightarrow> bool"
definition abstraction :: "('a::llty) \<Rightarrow> ('a,'b) nu \<Rightarrow> 'b \<Rightarrow> bool" ("(_/ \<nuLinkL> _ \<nuLinkR>/ _)" [15,15,15] 14)
  where abstraction_def: "abstraction p N x = (case N of Nu R \<Rightarrow> R (p,x))"

definition Nu_SE :: "('a::llty,'b) nu \<Rightarrow> 'b \<Rightarrow> bool" where
  Nu_SE_def:  "Nu_SE N x \<longleftrightarrow> (\<exists>p. p \<nuLinkL> N \<nuLinkR> x)"
definition NuPred :: "('a::llty,'b) nu \<Rightarrow> 'b \<Rightarrow> 'a set" (infix "\<nuPred>" 72) where
  NuPred_def: "NuPred N x = {p. (p \<nuLinkL> N \<nuLinkR> x) }"

lemma abstraction_SE: "p \<nuLinkL> N \<nuLinkR> x \<Longrightarrow> Nu_SE N x" by (auto simp add: Nu_SE_def)

definition Nu_Share :: "('a::sharable_llty,'b) nu \<Rightarrow> ('b \<Rightarrow> zint \<Rightarrow> 'b) \<Rightarrow> bool" where
  Nu_Share_def: "Nu_Share N f \<longleftrightarrow> (\<forall>z p x. (p \<nuLinkL> N \<nuLinkR> x) \<longrightarrow> (share p z \<nuLinkL> N \<nuLinkR> f x z))"

section\<open>Structures for construction\<close>

definition instr_comp (infixl "\<diamondop>" 55) where  "instr_comp = (o)"
text \<open> The operator @{term instr_comp} as an alias for the functional composition operator
   is defined  for the specific purpose for instruction composition in \<nu>-system.  \<close>

type_synonym label = ind
datatype 'a register = Register label 'a
  \<comment>\<open> Register label value
    where `label` is a free variable representing name of the register by its variable name\<close>
notation Register ("\<B_r>\<B_e>\<B_g>\<B_i>\<B_s>\<B_t>\<B_e>\<B_r> _ \<B_i>\<B_s> _" [4,4] 3)

definition RegisterSet :: "ind \<Rightarrow> 'a set \<Rightarrow> 'a register set" where
  RegisterSet_def: "RegisterSet name s = {r. case r of Register name' x \<Rightarrow> name' = name \<and> x \<in> s}"
notation RegisterSet ("_ \<B_n>\<B_a>\<B_m>\<B_e>\<B_d> _" [4,4] 3)
   and RegisterSet ("\<B_r>\<B_e>\<B_g>\<B_i>\<B_s>\<B_t>\<B_e>\<B_r> _ \<B_i>\<B_n> _" [4,4] 3)

definition PrettyAnd :: " 'a \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b " (infixr "and'_pair" 5)  where
  PrettyAnd_def: "(PrettyAnd) = Pair"
definition PrettyAndSet :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set " (infixr "and'_set" 5)  where
  PrettyAndSet_def: "(PrettyAndSet) = (\<times>)"
text \<open> `PrettyAnd` and `PrettyAndSet` are two alias for pairing operator and
  production set operator respectively, with special pretty printing settings to
  prevent parentheses in the printing. For example, both the term
  @{term "1 and_pair 2 and_pair 3"} and @{term "(1 and_pair 2) and_pair 3"}
  are printed identically, as "1 \<B_a>\<B_n>\<B_d> 2 \<B_a>\<B_n>\<B_d> 3". 
  It is useful to represent a collection of object which has some complicated inner structure
    (e.g. a binary tree) that is not intended to be displayed to user.\<close>
syntax "\<B_a>\<B_n>\<B_d>" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  ("_/ \<B_a>\<B_n>\<B_d> _" [6,5] 5)
translations
  "a \<B_a>\<B_n>\<B_d> b" <= "a and_pair b"
  "a \<B_a>\<B_n>\<B_d> b" <= "a and_set b"
  "a \<B_a>\<B_n>\<B_d> b \<B_a>\<B_n>\<B_d> c" <= "((a \<B_a>\<B_n>\<B_d> b) \<B_a>\<B_n>\<B_d> c)"

class register_collection = llty
  \<comment> \<open> A register_collection is always a llty, but NOT vice versa.
    register_collection ::= unit | register | register_collection \<times> register_collection.
    Also note register_collection is a binary tree.\<close>

datatype ('a, 'r) with_registers = WithRegisters 'a 'r (infix "with'_registers" 4)
type_notation with_registers ("_/ with _" [5,5] 4)
definition WithRegistersSet :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a with 'b) set" (infix "with'_set" 4) where
  WithRegistersSet_def: "WithRegistersSet s t = {x. case x of WithRegisters a b \<Rightarrow> a \<in>s \<and> b \<in> t}"
syntax "\<B_w>\<B_i>\<B_t>\<B_h>" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_/ \<B_w>\<B_i>\<B_t>\<B_h> _" [5,5] 4)
translations
  "a \<B_w>\<B_i>\<B_t>\<B_h> b" <= "a with_registers b"
  "a \<B_w>\<B_i>\<B_t>\<B_h> b" <= "a with_set b"

definition CodeBlock :: " 'a state \<Rightarrow> 'a state \<Rightarrow> bool" where
  CodeBlock_def: "CodeBlock var exp \<longleftrightarrow> (var = exp) \<and> (var \<noteq> STrap) "

definition SpecTop :: "prop \<Rightarrow> prop \<Rightarrow> prop" where
  SpecTop_def: "SpecTop \<equiv> (&&&)"
\<comment>\<open> SpecTop focus lemmata
  where the focus is the focused one or multiple HOL propositions intended to be constructed
    the lemmata are several propositions served as auxiliary facts, e.g. post conditions.\<close>
notation SpecTop ("_/ \<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>'_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>: _ " [1,1] 0)
lemma Specification_focus: "(P \<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>: Q) \<Longrightarrow> P" unfolding SpecTop_def by (rule conjunctionD1)
lemma Specification_aux: "(P \<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>: Q) \<Longrightarrow> Q" unfolding SpecTop_def by (rule conjunctionD2)
lemma Specification_rule_focus: "(P \<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>: Q) \<Longrightarrow> (Q \<Longrightarrow> P \<Longrightarrow> P') \<Longrightarrow> (P' \<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>: Q)"
    unfolding SpecTop_def by presburger
lemma Specification_rule_aux: "(P \<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>: Q) \<Longrightarrow> (Q \<Longrightarrow> Q') \<Longrightarrow> (P \<B_a>\<B_u>\<B_x>\<B_i>\<B_l>\<B_i>\<B_a>\<B_r>\<B_y>_\<B_f>\<B_a>\<B_c>\<B_t>\<B_s>: Q')"
    unfolding SpecTop_def  by presburger

end
  