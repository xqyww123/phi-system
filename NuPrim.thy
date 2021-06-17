(* KEEP IT SIMPLE AND STUPID *)

theory NuPrim
  imports Main
  abbrevs "is" = "\<^bold>i\<^bold>s"
      and "as" = "\<^bold>a\<^bold>s"
      and "register" = "\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r"
      and "in" = "\<^bold>i\<^bold>n"
      and "with" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
      and "auxiliary_facts" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "auxfacts" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "proc" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
      and "param" = "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m"
      and ";;" = "\<bbar>"
begin

text \<open>The fundamental theory for \<nu>-system\<close>

section Preliminary

declare [[quick_and_dirty = true]]
bundle show_more1 = [[show_hyps = true, show_types = true, show_sorts = true]]
bundle show_more = [[show_hyps = true, show_types = true]]

named_theorems \<nu>share
named_theorems \<nu>equable

subsubsection \<open>Syntax and Notations\<close>

consts "ARBITRARY___" :: 'a ("\<cdots>") \<comment>\<open>merely a sugar for documenting\<close>

definition PropBlock :: "prop \<Rightarrow> prop" ("\<medium_left_bracket> _ \<medium_right_bracket>" [0] 1000) where "PropBlock p \<equiv> p"
  \<comment>\<open>The block of proposition has specific meaning in \<nu>-system.
  @{prop "A \<Longrightarrow> B \<Longrightarrow> C"} represents an forward construction rule to finally construct @{term C}.
  The construction rule could be high-order parametric, e.g. @{prop "A \<Longrightarrow> \<medium_left_bracket> B \<Longrightarrow> C \<Longrightarrow> D \<medium_right_bracket> \<Longrightarrow> E"},
    and in those cases the high-order parameter is wrapped by @{term Pure.prop} to become an atomic
    premise in order to disambiguate with the semantics of nested hypothesises.\<close>
lemmas  PropBlock_I = PropBlock_def[THEN equal_elim_rule2]
lemmas  PropBlock_D = PropBlock_def[THEN equal_elim_rule1]

syntax
  "_pretty_and_" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  ("_/ \<^bold>a\<^bold>n\<^bold>d _" [4,3] 3)
  "_linebreak_" :: "logic \<Rightarrow> logic" ("//\<zero_width_space>_" [3] 3)
  "_linebreak_collection_" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  ("_//\<invisible_separator>_" [4,3] 3)
  "_with_" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _" [2,1] 1)
  (* "_is_" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>i\<^bold>s _" [5,5] 4)
  "_in_" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>i\<^bold>n _" [5,5] 4)
  "_as_" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>a\<^bold>s _" [5,5] 4) *)
translations
  "a \<^bold>a\<^bold>n\<^bold>d b \<^bold>a\<^bold>n\<^bold>d c" <= "(a \<^bold>a\<^bold>n\<^bold>d b) \<^bold>a\<^bold>n\<^bold>d c"
  "_linebreak_collection_ a (_linebreak_collection_ b c)" <= "_linebreak_collection_ (_linebreak_collection_ a b) c"
text \<open> `_pretty_and_` suppresses parentheses in the printing. For example, both the term
  "1 and 2 and 3" and  "(1 and 2) and 3" are printed identically, as 1 \<^bold>a\<^bold>n\<^bold>d 2 \<^bold>a\<^bold>n\<^bold>d 3". 
  It is useful to represent a collection of object which has some complicated inner structure
    (e.g. a binary tree) that is not intended to be displayed to user.\<close>

named_theorems typing_expn "expansion theorems for abstractions"

datatype zint = Gz | Gi int
text\<open> Type @{typ zint} is used to represent ownership. @{term "Gi i"} represents
  $2^{-i}$ part of the ownership, and @{term "Gi 0"} is the total. @{term Gz} represents
  some ownership of unknown quantity. Any value of @{type zint} represents
  some part (or the total) of ownership. The empty ownership is represented
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

section\<open>Low representation for semantics\<close>

datatype llty = la_i nat | la_p nat | la_s llty
  | la_a llty nat | la_z | la_C llty llty

class lrep = fixes llty :: "'a itself \<Rightarrow> llty"
  \<comment>\<open>The class for basic low level types\<close>

text \<open>The ability for memory allocation\<close>
class zero_lrep = lrep +
  fixes lty_zero :: "'a"

text \<open>The ability for equality comparison\<close>
class ceq_lrep = lrep +
  fixes ceqable :: "('a * 'a) \<Rightarrow> bool"
  fixes ceq :: "('a * 'a) \<Rightarrow> bool"
  assumes ceqable_sym[ac_simps]: "ceqable (x,y) = ceqable (y,x)"
  assumes ceq_refl[simp]: "ceqable (x,x) \<Longrightarrow> ceq (x,x)"
  assumes ceq_sym[ac_simps]: "ceqable (x,y) \<Longrightarrow> ceq (x,y) \<longleftrightarrow> ceq (y,x)"
  assumes ceq_trans: "ceqable (x,y) \<Longrightarrow> ceqable (y,z) \<Longrightarrow> ceqable (x,z)
    \<Longrightarrow> ceq(x,y) \<Longrightarrow> ceq (y,z) \<Longrightarrow> ceq (x,z)"

class sharable_lrep = lrep + 
  fixes revert :: "'a * 'a \<Rightarrow> bool"
    and sharable :: "'a \<Rightarrow> bool"
    and share :: "'a \<Rightarrow> zint \<Rightarrow> 'a"
    and dpriv :: "'a \<Rightarrow> 'a"
  assumes revert_refl[simp]: "revert (x,x)"
  assumes revert_sym[ac_simps]: "revert (x,y) \<longleftrightarrow> revert (y,x)"
  assumes revert_trans: "revert (x,y) \<Longrightarrow> revert (y,z) \<Longrightarrow> revert (x,z)"
  assumes share_id[simp]: "share x (Gi 0) = x"
  assumes share_assoc[simp]: "share (share x a) b = share x (a + b)"

class naive_lrep = sharable_lrep +
  assumes marsharable_sha[simp]: "sharable x = True"
  assumes marsharable_dp[simp]: "dpriv = id"
  assumes marsharable_sh[simp]: "share = K"
  assumes marsharable_rt[simp]: "revert xy = True"  

datatype ('a,'b) nu = Nu "('a::lrep) * 'b \<Rightarrow> bool"

definition NuTyp :: "'b \<Rightarrow> ('a::lrep,'b) nu \<Rightarrow> 'a set" (infix "\<tycolon>" 15) \<comment>\<open>shortcut keys ":ty:"\<close>
  where "(x \<tycolon> N) = {p. case N of Nu R \<Rightarrow> R (p,x) }"
abbreviation NuTyping :: "('a::lrep) \<Rightarrow> ('a,'b) nu \<Rightarrow> 'b \<Rightarrow> bool" ("(_/ \<nuLinkL> _ \<nuLinkR>/ _)" [27,15,27] 26) \<comment>\<open>shortcut keys "--<" and ">--"\<close>
  where  "(p \<nuLinkL> N \<nuLinkR> x) \<equiv> p \<in> (x \<tycolon> N)"
definition Inhabited :: " 'a set \<Rightarrow> bool" where "Inhabited s \<equiv> (\<exists>x. x \<in> s)"
abbreviation InhabitTyp :: " 'b \<Rightarrow> ('a::lrep,'b) nu \<Rightarrow> bool" (infix "\<ratio>" 15)  \<comment>\<open>shortcut keys ":TY:"\<close>
  where  "(x \<ratio> N) \<equiv> Inhabited (x \<tycolon> N)"
text \<open>The @{term "x \<tycolon> N"} is a predication specifying concrete values,
  e.g. @{prop "a_concrete_int32 \<in> ((42::nat) \<tycolon> N 32) "} and also @{prop "state \<in> State ((42 \<tycolon> N) \<times> (24 \<tycolon> N) \<times> \<cdots> )"}.
  It constitutes basic elements in specification.
  The @{prop "p \<nuLinkL> N \<nuLinkR> x"} as the abbreviation of $p \<in> (x \<tycolon> N)$ is an abstraction between concrete value @{term p} and
  abstracted {\it image} @{term x} via the \<nu>-{\it abstractor} @{term N} which defines the abstraction relationship itself.
  The next @{prop "x \<ratio> N"} is a proposition stating @{term x} is an image of abstractor @{term N} and therefore
  the \<nu>-type @{term "x \<tycolon> N"} is inhabited. Basically it is used to derive implicated conditions of images,
  e.g. @{prop "(42 \<ratio> N 32) \<Longrightarrow> 42 < 2^32"}\<close>

lemma [simp]: "p \<nuLinkL> Nu R \<nuLinkR> x \<equiv> R (p,x)" unfolding NuTyp_def by simp
lemma inhabited[dest]: "p \<nuLinkL> N \<nuLinkR> x \<Longrightarrow> x \<ratio> N" unfolding Inhabited_def by auto
lemma [elim]: "Inhabited (U \<times> V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> PROP C) \<Longrightarrow> PROP C" unfolding Inhabited_def by auto

definition Nu_Share :: "('a::sharable_lrep,'b) nu \<Rightarrow> ('b \<Rightarrow> zint \<Rightarrow> 'b) \<Rightarrow> bool"
  where  "Nu_Share N f \<longleftrightarrow> (\<forall>z p x. (p \<nuLinkL> N \<nuLinkR> x) \<longrightarrow> (share p z \<nuLinkL> N \<nuLinkR> f x z))"
lemma \<nu>share_masharable[\<nu>share]: "Nu_Share N K" for N :: "('a::naive_lrep, 'b) nu" unfolding Nu_Share_def by simp
definition \<nu>Equalable :: "('a::ceq_lrep, 'b) nu \<Rightarrow> ('b \<times> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "\<nu>Equalable N f \<longleftrightarrow> (\<forall>p1 p2 x1 x2. (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> N \<nuLinkR> x2) \<longrightarrow> ceqable (p1,p2) = f (x1,x2))"

lemma K_rew: "(\<lambda>x. c) =  (K c)" by auto
lemma [simp]: "\<nu>Equalable N (\<lambda>x. c) = \<nu>Equalable N (K c)" by (auto simp add: K_rew)
lemma [simp]: "Nu_Share N (\<lambda>x z. x) = Nu_Share N K" by (auto simp add: K_rew)

section\<open>Structures for construction\<close>

subsubsection \<open>Auxiliary name tag\<close>

datatype name_tag = NAME_TAG "unit \<Rightarrow> unit"
datatype name2_tag = NAME2_TAG "unit \<Rightarrow> unit \<Rightarrow> unit"
lemma [cong]: "NAME_TAG x \<equiv> NAME_TAG x" and [cong]: "NAME2_TAG y \<equiv> NAME2_TAG y" using reflexive .
syntax "_NAME_" :: "idt \<Rightarrow> name_tag" ("NAME _" [0] 1000)
  "_NAME2_" :: "idt => idt => name_tag" ("NAME2 _ _" [0,0] 1000)
translations "NAME name" == "CONST NAME_TAG (\<lambda>name. ())"
  "NAME2 name1 name2" == "CONST NAME2_TAG (\<lambda>name1 name2. ())"

definition Named :: "name_tag \<Rightarrow> 'a \<Rightarrow> 'a" where "Named name x = x" \<comment>\<open>name tag\<close>
syntax "_named_" :: "logic \<Rightarrow> idt \<Rightarrow> logic" (infix "named" 4)
translations "x named name" == "CONST Named (NAME name) x"
ML_val \<open> Syntax.read_term @{context} "AAA named yy" \<close>

subsubsection \<open>Register and its collection\<close>

datatype void = void \<comment>\<open> End of the stack \<close>
definition Void :: "void set" where "Void = {void}" 
text \<open>The name `void` coincides that, when a procedure has no input arguments,
  the \<nu>-type for the input would exactly be @{term Void}. \<close>
lemma [simp,intro]: "void \<in> Void" unfolding VoidTy_def by simp
translations "a" <= "a \<^bold>a\<^bold>n\<^bold>d CONST Void"

datatype 'a register = Register name_tag 'a
  \<comment>\<open> Register label value
    where `label` is a free variable representing name of the register by its variable name\<close>
syntax "_register_as_" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a register" ("\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r _ \<^bold>a\<^bold>s _" [5,5] 4)
translations "_register_as_ name exp" == "CONST Register (NAME name) exp"
term "Register (NAME a) b"

definition RegisterTy :: "name_tag \<Rightarrow> 'a set \<Rightarrow> 'a register set" where
  RegisterTy_def: "RegisterTy name s = {r. case r of Register name' x \<Rightarrow> name' = name \<and> x \<in> s}"
syntax "_register_set_" :: "idt \<Rightarrow> 'a set \<Rightarrow> 'a register set" ("\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r _ \<^bold>i\<^bold>n _" [5,5] 4)
translations "_register_set_ name S" == "CONST RegisterTy (NAME name) S"
lemma [simp]: "Register v x \<in> RegisterTy v' T \<longleftrightarrow> v = v' \<and> x \<in> T" unfolding RegisterTy_def by  simp

definition And :: " 'a \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b " (infixr "and'_pair" 3)  where "And = Pair"
definition AndTy :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set " (infixr "and'_ty" 3)  where  "AndTy = (\<times>)"
translations
  "a \<^bold>a\<^bold>n\<^bold>d b" <= "a and_pair b"
  "a \<^bold>a\<^bold>n\<^bold>d b" <= "a and_ty b"
lemma [simp]: "(a and_pair b) \<in> (A and_ty B) \<longleftrightarrow> a \<in> A \<and> b \<in> B" unfolding AndTy_def And_def by simp

class register_collection = lrep
  \<comment> \<open> A register_collection is always a lrep, but a lrep may not a register collection.
    register_collection ::= void | register | register_collection \<times> register_collection.
    Also note register_collection is a binary tree, not only a register list.\<close>

instantiation void :: register_collection begin
definition llty_void :: "void itself \<Rightarrow> llty" where [simp]: "llty_void _ = la_z"
instance by standard
end

instantiation register :: (lrep) register_collection begin
definition register_unit :: "'a register itself \<Rightarrow> llty" where [simp]: "register_unit _ = la_z"
instance by standard
end

instantiation prod :: (lrep,lrep) lrep begin
definition llty_prod :: "('a \<times> 'b) itself \<Rightarrow> llty" where [simp]: "llty_prod _ = la_C (llty TYPE('a)) (llty TYPE('b))"
instance by standard
end

instantiation prod :: (register_collection,register_collection) register_collection begin instance by standard end

subsubsection \<open>The \<nu>-system VM and Procedure construction structures\<close>

definition Stack_Delimiter (infixr "\<bbar>" 13) where [simp]:"Stack_Delimiter = (\<times>)"
definition End_of_Contextual_Stack :: " 'a \<Rightarrow> 'a " where "End_of_Contextual_Stack x = x" \<comment> \<open>A tag for printing sugar\<close>
translations "a" <= "a \<bbar> CONST End_of_Contextual_Stack x" \<comment> \<open>hide the end\<close>
lemma [simp]: "(a,b) \<in> A \<bbar> B \<longleftrightarrow> a \<in> A \<and> b \<in> B" unfolding Stack_Delimiter_def by simp

text \<open>The procedure construction context.\<close>
datatype ('a, 'r) "proc_ctx"  = Proc_Ctx 'a 'r
declare proc_ctx.split[split]
type_notation "proc_ctx" ("_/ \<flower> _" [2,2] 1)
definition Proc_CtxTy :: " ('a::lrep) set \<Rightarrow> ('b::register_collection) set \<Rightarrow> ('a \<flower> 'b) set" (infix "\<flower>" 4)
  where "Proc_CtxTy s t = {x. case x of Proc_Ctx a b \<Rightarrow> a \<in>s \<and> b \<in> t}"
syntax "_no_registers_" :: logic ("\<^bold>n\<^bold>o \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r\<^bold>s")
   "_empty_stack_" :: logic ("\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k")
translations "x \<flower> \<^bold>n\<^bold>o \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r\<^bold>s" == "x \<flower> CONST Void"
  "\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k \<flower> x" <= "CONST End_of_Contextual_Stack s \<flower> x"
term "A \<bbar> B \<bbar> End_of_Contextual_Stack R \<flower> Void"
lemma [simp]: "(Proc_Ctx s r) \<in> (T \<flower> U) \<equiv> s \<in> T \<and> r \<in> U" by (simp add: Proc_CtxTy_def)
lemma Proc_CtxTy_elim[elim]: "c \<in> (T \<flower> U) \<Longrightarrow> (\<And>s r. c = (Proc_Ctx s r) \<Longrightarrow> s \<in> T \<Longrightarrow> r \<in> U \<Longrightarrow> C) \<Longrightarrow> C" by (cases c) auto
lemma [dest]: "Proc_Ctx s r \<in> (T \<flower> U) \<Longrightarrow> s \<in> T" and [dest]: "Proc_Ctx s r \<in> (T \<flower> U) \<Longrightarrow> r \<in> U" by simp+
lemma Proc_CtxTy_intro[intro]: "s \<in> T \<Longrightarrow> r \<in> U \<Longrightarrow> Proc_Ctx s r \<in> (T \<flower> U)" by (simp add: Proc_CtxTy_def)


datatype 'a state = StatOn 'a | STrap | SNeg
text\<open> The basic state of the \<nu>-system virtual machine is represented by type @{typ "'a state"}.
  The valid state @{term "StatOn p"} essentially has two major form, one without registers and another one with them,
      \<^item> @{term "StatOn (x1, x2, \<cdots>, xn, void)"},
      \<^item> @{term "StatOn (Proc_Ctx (x1, x2, \<cdots>, xn, void ) (\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r r1 \<^bold>a\<^bold>s y1 and_pair \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r r2 \<^bold>a\<^bold>s y2 and_pair \<cdots>))"},
  where @{term "(x1, x2, \<cdots>, xn, void)"} represents the stack in the state, with @{term x\<^sub>i} as the i\<^sup>t\<^sup>h element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term SNeg} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term SNeg} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>
declare state.split[split]
definition StrictStateTy :: " 'a set \<Rightarrow> 'a state set" ("\<S_S> _" [56] 55)
  where "\<S_S> T = {s. case s of StatOn x \<Rightarrow> x \<in> T | STrap \<Rightarrow> False | SNeg \<Rightarrow> False}"
definition LooseStateTy :: " 'a set \<Rightarrow> 'a state set" ("\<S> _" [56] 55)
  where "\<S> T = {s. case s of StatOn x \<Rightarrow> x \<in> T | STrap \<Rightarrow> False | SNeg \<Rightarrow> True}"
lemma [simp]: "StatOn x \<in> \<S_S> T \<equiv> x \<in> T" and [simp]: "\<not> (SNeg \<in> \<S_S> T)" and [simp]: "\<not> (STrap \<in> \<S_S> T)"
  and [simp]: "StatOn x \<in> \<S> T \<equiv> x \<in> T" and [simp]: "SNeg \<in> \<S> T" and [simp]: "\<not> (STrap \<in> \<S> T)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
lemma [dest]: "s \<in> \<S_S> T \<Longrightarrow> Inhabited T" unfolding Inhabited_def by (cases s) auto
    \<comment>\<open>The inhabited property can be inferred from @{term StrictStateTy} only rather than @{term LooseStateTy}. \<close>
lemma StrictStateTy_elim: "s \<in> \<S_S> T \<Longrightarrow> (\<And>x. s = StatOn x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma LooseStateTy_elim: "s \<in> \<S> T \<Longrightarrow> (\<And>x. s = StatOn x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> (s = SNeg \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma LooseStateTy_upgrade: "s \<in> \<S> T \<Longrightarrow> s \<noteq> SNeg \<Longrightarrow> s \<in> \<S_S> T" by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> \<S_S> T \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> SNeg \<Longrightarrow> s \<in> \<S_S> T) \<Longrightarrow> s \<in> \<S> T" by (cases s) auto

definition ExTyp :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" (binder "\<exists>* " 10) where "ExTyp T = {x. (\<exists>z. x \<in> T z)}"
lemma [simp]: "x \<in> ExTyp T \<equiv> (\<exists>z. x \<in> T z)" unfolding ExTyp_def by auto
lemma [simp]: "\<S_S> (ExTyp T) = (\<exists>* x. \<S_S> (T x))" unfolding ExTyp_def
proof auto
  fix x z show "x \<in> \<S_S> {x. \<exists>z. x \<in> T z} \<Longrightarrow> \<exists>z. x \<in> \<S_S> T z" and "x \<in> \<S_S> T z \<Longrightarrow> x \<in> \<S_S> {x. \<exists>z. x \<in> T z}" by (cases x; auto)+
qed
lemma [simp]: "\<S> (ExTyp T) = (\<exists>* x. \<S> (T x))" unfolding ExTyp_def
proof auto
  fix x z show "x \<in> \<S> {x. \<exists>z. x \<in> T z} \<Longrightarrow> \<exists>z. x \<in> \<S> T z " and "x \<in> \<S> T z \<Longrightarrow> x \<in> \<S> {x. \<exists>z. x \<in> T z}" by (cases x; auto)+
qed

abbreviation Procedure :: "('a \<Rightarrow> 'b state) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("\<^bold>p\<^bold>r\<^bold>o\<^bold>c _ \<llangle> _ \<longmapsto> _ \<rrangle>" [4,2,2] 5)
  where "Procedure f T U \<equiv> (\<forall>a. a \<in> T \<longrightarrow> f a \<in> \<S> U)"

definition bind :: " 'a state \<Rightarrow> ('a \<Rightarrow> 'b state) \<Rightarrow> 'b state " \<comment>\<open>monadic bind\<close>
  where "bind s f = (case s of StatOn x \<Rightarrow> f x | STrap \<Rightarrow> STrap | SNeg \<Rightarrow> SNeg)"
definition instr_comp :: "('a \<Rightarrow> 'b state) \<Rightarrow> ('b \<Rightarrow> 'c state) \<Rightarrow> 'a \<Rightarrow> 'c state"  (infixr "\<nuInstrComp>" 75) 
  where "instr_comp f g s = bind (f s) g" \<comment>\<open>It is NOT monadic `then` operator (\<then>)!\<close>
definition nop :: " 'a \<Rightarrow> 'a state" where "nop = StatOn" \<comment>\<open>the instruction `no-operation`\<close>
definition call :: "('a \<Rightarrow> 'b state) \<Rightarrow> ('a \<flower> 'r) \<Rightarrow> ('b \<flower> 'r) state"
  where "call f s = (case s of Proc_Ctx x r \<Rightarrow> bind (f x) (\<lambda>x. StatOn (Proc_Ctx x r)))"
definition begin_proc_ctx :: " 'a \<Rightarrow> ('a \<flower> void) state" where "begin_proc_ctx x = StatOn (Proc_Ctx x void)"
definition end_proc_ctx :: " 'a \<flower> 'b \<Rightarrow> 'a state" where "end_proc_ctx ctx = (case ctx of Proc_Ctx x y \<Rightarrow> StatOn x)"

lemma nop: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<llangle> T \<longmapsto> T \<rrangle>" unfolding nop_def by auto
lemma call: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<llangle> U \<longmapsto> V \<rrangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c call f \<llangle> U \<flower> W \<longmapsto> V \<flower> W \<rrangle>"
  unfolding call_def by  (auto simp add: bind_def)
lemma end_proc_ctx: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c end_proc_ctx \<llangle> T \<flower> R \<longmapsto> T \<rrangle>" unfolding end_proc_ctx_def by auto

subsection \<open>Top-level constructions and rules\<close>

definition CurrentConstruction :: " 'a state \<Rightarrow> 'a set \<Rightarrow> bool " ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n/ _" [1000,5] 0)
  where "CurrentConstruction s S \<longleftrightarrow> s \<in> \<S_S> S"
definition PendingConstruction :: " ('a \<Rightarrow> 'b state) \<Rightarrow> 'a state \<Rightarrow> 'b set \<Rightarrow> bool " ("\<B_p>\<B_e>\<B_n>\<B_d>\<^bold>i\<^bold>n\<B_g> _ \<^bold>o\<^bold>n _ \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,1] 0)
  where "PendingConstruction f s S \<longleftrightarrow> bind s f \<in> \<S> S"

definition CodeBlock :: " 'a state \<Rightarrow> 'b => 'b set \<Rightarrow> ('b \<Rightarrow> 'a state) \<Rightarrow> bool" where
  CodeBlock_def: "CodeBlock stat arg ty prog \<longleftrightarrow> (arg \<in> ty \<and> prog arg = stat \<and> stat \<noteq> SNeg)"
syntax "_codeblock_exp_" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> bool"  ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _  \<^bold>a\<^bold>s '\<open>_'\<close> \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<B_r>\<B_g>\<B_u>\<B_m>\<B_e>\<B_n>\<B_t>\<^bold>s '\<open>_'\<close> " [100,0,0] 3)
syntax "_codeblock_" :: "idt \<Rightarrow> logic \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<B_r>\<B_g>\<B_u>\<B_m>\<B_e>\<B_n>\<B_t>\<^bold>s '\<open>_'\<close>" [100,0] 3)
translations "_codeblock_ v ty" <= "CONST CodeBlock v arg ty exp"
(* translations "_codeblock_exp_ v exp ty" <= "CONST CodeBlock v arg ty exp" *)

definition Fact :: "ind \<Rightarrow> bool \<Rightarrow> prop" ("\<^item> _ : _" [5,0] 4) where Fact_def:"Fact label P \<equiv>Trueprop P"

term "PROP (Fact a b) &&& PROP (Fact c d)"
definition NoFact :: "prop" ("\<B_n>\<B_o>\<B_t>\<B_h>\<^bold>i\<^bold>n\<B_g>") where "NoFact \<equiv> Trueprop True"
definition AndFact :: "prop \<Rightarrow> prop \<Rightarrow> prop" (infixr "and'_fact" 3) where AndFact_def:"AndFact \<equiv> (&&&)"
translations "_linebreak_collection_ P Q" <= "CONST AndFact P Q"
lemma NoFact: "PROP NoFact" unfolding NoFact_def by fast

definition SpecTop :: "prop \<Rightarrow> prop \<Rightarrow> prop" where SpecTop_def: "SpecTop \<equiv> (&&&)"
\<comment>\<open> SpecTop focus lemmata
  where the focus is the focused one or multiple HOL propositions intended to be constructed
    the lemmata are several propositions served as auxiliary facts, e.g. post conditions.\<close>
notation SpecTop ("SPEC'_TOP _ _")
  and SpecTop ("_/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s:/ _ " [1,1] 0)
lemma SpecTop_focus[dest]: "(PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP Q) \<Longrightarrow> PROP P" unfolding SpecTop_def conjunction_imp .
lemma SpecTop_facts[dest]: "(PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP Q) \<Longrightarrow> PROP Q" unfolding SpecTop_def conjunction_imp .
lemma SpecTop_imp: "(PROP SpecTop (PROP P) (PROP L) \<Longrightarrow> PROP C) \<equiv> (PROP P \<Longrightarrow> PROP L \<Longrightarrow> PROP C)"
  unfolding SpecTop_def conjunction_imp .
lemma SpecTop_I: "PROP P \<Longrightarrow> PROP L \<Longrightarrow> PROP SpecTop (PROP P) (PROP L)" unfolding SpecTop_def using conjunctionI .
(* lemma Specification_rule_focus: "(P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP Q) \<Longrightarrow> (PROP Q \<Longrightarrow> P \<Longrightarrow> P') \<Longrightarrow> (P' \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP Q)"
    unfolding SpecTop_def by presburger
lemma Specification_rule_aux: "(P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: Q) \<Longrightarrow> (Q \<Longrightarrow> Q') \<Longrightarrow> (P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: Q')"
    unfolding SpecTop_def  by presburger *)

theorem apply_proc: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n S \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L ) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<llangle> S \<longmapsto> T \<rrangle> \<Longrightarrow>
  (\<B_p>\<B_e>\<B_n>\<B_d>\<^bold>i\<^bold>n\<B_g> f \<^bold>o\<^bold>n s \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L )"
  unfolding CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp by (rule SpecTop_I) auto

theorem  accept_proc: "\<medium_left_bracket> \<And>s. CodeBlock s a S f \<Longrightarrow> (\<B_p>\<B_e>\<B_n>\<B_d>\<^bold>i\<^bold>n\<B_g> g \<^bold>o\<^bold>n s \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L ) \<medium_right_bracket> \<Longrightarrow>
  CodeBlock s' a S (f \<nuInstrComp> g) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: (PROP L))" for L :: "prop"
  unfolding PropBlock_def CodeBlock_def instr_comp_def CurrentConstruction_def PendingConstruction_def
proof (rule SpecTop_I)
  assume a: "(\<And>s. a \<in> S \<and> f a = s \<and> s \<noteq> SNeg \<Longrightarrow> SPEC_TOP (bind s g \<in> \<S> T) (PROP L))" and b: " a \<in> S \<and> bind (f a) g = s' \<and> s' \<noteq> SNeg"
  from b have sa: "a \<in> S \<and> f a = f a \<and> f a \<noteq> SNeg" by (cases "f a") (auto simp add: bind_def)
  note th = a[OF sa, simplified b[THEN conjunct1]]
  from th[THEN SpecTop_focus] show "s' \<in> \<S_S> T" using b by (blast intro: LooseStateTy_upgrade)
  from th[THEN SpecTop_facts] show "PROP L" .
qed

theorem start_construction: "CodeBlock s a S begin_proc_ctx \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n (S \<flower> Void) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: (PROP NoFact)"
  unfolding begin_proc_ctx_def CodeBlock_def CurrentConstruction_def by (rule SpecTop_I; (rule NoFact)?) auto

theorem finish_construction: "\<medium_left_bracket>\<And>a s. CodeBlock s a S f \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n (T \<flower> R) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L \<medium_right_bracket>
  \<Longrightarrow> f' = f \<nuInstrComp> end_proc_ctx \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<llangle> S \<longmapsto> T \<rrangle>"
    unfolding PropBlock_def CodeBlock_def
proof
  assume rule:"(\<And>a s. a \<in> S \<and> f a = s \<and> s \<noteq> SNeg \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<B_r>\<B_e>\<^bold>s\<B_u>\<B_l>\<B_t>\<^bold>s \<^bold>i\<^bold>n (T \<flower> R) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)"
    and def: "f' = f \<nuInstrComp> end_proc_ctx"
  fix a show "a \<in> S \<longrightarrow> f' a \<in> \<S> T " unfolding def proof
    assume a: "a \<in> S"
    moreover note rule[of a "f a", unfolded CurrentConstruction_def, simplified, THEN SpecTop_focus] 
    ultimately show "(f \<nuInstrComp> end_proc_ctx) a \<in> \<S> T" unfolding instr_comp_def bind_def end_proc_ctx_def
      using LooseStateTy_introByStrict by (cases "f a") auto
  qed
qed

definition ParamTag :: " 'a \<Rightarrow> prop" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m") where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> Trueprop True"
lemma ParamTag_E: "PROP \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" unfolding ParamTag_def using TrueI .
  \<comment>\<open>A tag used to indicate a parameter should be specified during application. It retains the order of the parameters to be specified.
  For example, "@{prop "\<And>bit_width value. PROP \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_width \<Longrightarrow> PROP \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c const_nat \<llangle> R \<longmapsto> (value \<tycolon> NuNat bit_width) \<rrangle>"},
    the first parameter `?bit_width` will be specified first and then the "?value".\<close>

end
