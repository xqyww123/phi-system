(* KEEP IT SIMPLE AND STUPID *)

theory NuPrim \<comment> \<open>The Primary Theory of the \<nu>-System\<close>
  imports Main "HOL-Library.Monad_Syntax"
  abbrevs "is" = "\<^bold>i\<^bold>s"
      and "as" = "\<^bold>a\<^bold>s"
      and "register" = "\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r"
      and "in" = "\<^bold>i\<^bold>n"
      and "with" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
      and "auxiliary_facts" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "auxfacts" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "proc" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
      and "map" = "\<^bold>m\<^bold>a\<^bold>p"
      and "param" = "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m"
      and ";;" = "\<boxbar>"
      and cast = "\<^bold>c\<^bold>a\<^bold>s\<^bold>t"
      and andalso = "\<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o"
      and address = "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s"
begin

text \<open>The fundamental theory for \<nu>-system\<close>

section Preliminary

declare [[quick_and_dirty = true]]
bundle show_more1 = [[show_hyps = true, show_types = true, show_sorts = true]]
bundle show_more = [[show_hyps = true, show_types = true]]

named_theorems \<nu>intro "\<nu>-type introduction rules" and \<nu>elim "\<nu>-type elimination rules"
  \<comment> \<open>\<nu> introduction and elimination rules destructs and reconstructs \<nu> typings.
    They are not required in the program construction,
    and generally it is not expected to destruct \<nu> typings during the construction.
    Therefore, they are not included in the standard introduction and elimination rules.
    However they are quite useful in primitive proofs for properties (e.g. cast) and instructions. \<close>
named_theorems \<nu>share and \<nu>disposable and \<nu>equable
named_theorems \<nu>cast "introduction rules for casting"
named_theorems \<nu>def \<open>primitive definitions used to unfold in proofs of primitive instructions.\<close>
  and \<nu>address_def \<open>primitive definitions for unfolding in proofs for address\<close>
named_theorems \<nu>address_getter and \<nu>address_mapper

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

subsection\<open>LRep: Low Representation for semantics\<close>

text \<open>The semantic framework follows a style of shallow embedding, where semantics for different type (e.g. integers, floats)
  are modelled by different Isabelle type. Model types are constrained by the base type class {\it lrep} and types representing
  objects that supports certain features are constrained by specific sub-classes which extend the base class {\it lrep} finally. \<close>

datatype llty = la_i nat | la_p nat | la_s llty | la_a llty nat | la_z | la_C llty llty
  \<comment> \<open>LLVM types representing integers in specified bit length, pointers in the given space, structures of given content
  (usually a list by @{term la_C}), arrays of given content and fixed length, abstract type filtered during code extraction,
  and the list constructor which is used in argument list and structure's filed list,  respectively. \<close>

class lrep = \<comment>\<open>The basic class for types modelling concrete objects\<close>
  fixes llty :: "'a itself \<Rightarrow> llty" \<comment> \<open>The LLVM type to which the model type corresponds\<close>
  fixes disposable :: " 'a set " \<comment> \<open>Whether a value could be thrown away freely\<close>

class zero_lrep = lrep + \<comment> \<open>memory allocation\<close>
  fixes lty_zero :: "'a" \<comment> \<open>The zero value to what concrete objects are initialized.\<close>

class ceq_lrep = lrep + \<comment> \<open>equality comparison\<close>
  fixes ceqable :: "('a * 'a) \<Rightarrow> bool" \<comment> \<open>Whether two values could be compared for equality\<close>
  fixes ceq :: "('a * 'a) \<Rightarrow> bool" \<comment> \<open>The equality of two values.
    It is only valid when the two values could be compared, that the @{term ceqable} for them is true.\<close>
  assumes ceqable_sym[ac_simps]: "ceqable (x,y) = ceqable (y,x)"
  assumes ceq_refl[simp]: "ceqable (x,x) \<Longrightarrow> ceq (x,x)"
  assumes ceq_sym[ac_simps]: "ceqable (x,y) \<Longrightarrow> ceq (x,y) \<longleftrightarrow> ceq (y,x)"
  assumes ceq_trans: "ceqable (x,y) \<Longrightarrow> ceqable (y,z) \<Longrightarrow> ceqable (x,z)
    \<Longrightarrow> ceq(x,y) \<Longrightarrow> ceq (y,z) \<Longrightarrow> ceq (x,z)"

class sharable_lrep = lrep + \<comment> \<open>for objects whose the ownership can be shared \<close>
  fixes shareable :: "'a set" \<comment> \<open>Whether the ownership of a value could be shared.
      It is a predicate giving the precise control to decide on the shareability for each value.\<close>
    and share :: "zint \<Rightarrow> 'a \<Rightarrow> 'a"
    and revert :: "'a * 'a \<Rightarrow> bool"
    and dpriv :: "'a \<Rightarrow> 'a"
  assumes revert_refl[simp]: "revert (x,x)"
  assumes revert_sym[ac_simps]: "revert (x,y) \<longleftrightarrow> revert (y,x)"
  assumes revert_trans: "revert (x,y) \<Longrightarrow> revert (y,z) \<Longrightarrow> revert (x,z)"
  assumes share_id[simp]: "share (Gi 0) = id"
  assumes share_assoc[simp]: "share b (share a x) = share (a + b) x"

class naive_lrep = sharable_lrep +
  assumes [simp]: "disposable = UNIV"
  assumes [simp]: "shareable = UNIV"
  assumes [simp]: "dpriv = id"
  assumes [simp]: "share z = id"
  assumes [simp]: "revert xy = True"  

subsection \<open>The \<nu>-type\<close>

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

definition Nu_Share :: "('a::sharable_lrep,'b) nu \<Rightarrow> 'b set \<Rightarrow> (zint \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool"
  where  "Nu_Share N s f \<longleftrightarrow> (\<forall>z p x. x \<in> s \<and>(p \<nuLinkL> N \<nuLinkR> x) \<longrightarrow> p \<in> shareable \<and> (share z p \<nuLinkL> N \<nuLinkR> f z x))"
definition \<nu>Equalable :: "('a::ceq_lrep, 'b) nu \<Rightarrow> ('b \<times> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "\<nu>Equalable N f \<longleftrightarrow> (\<forall>p1 p2 x1 x2. (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> N \<nuLinkR> x2) \<longrightarrow> ceqable (p1,p2) = f (x1,x2))"
definition \<nu>Disposable :: " ('a::lrep) set \<Rightarrow> bool " where [\<nu>def]: "\<nu>Disposable T \<longleftrightarrow> (\<forall>x. x \<in> T \<longrightarrow> x \<in> disposable)"

lemma [\<nu>share]: "Nu_Share N UNIV (K id)" for N :: "('a::naive_lrep, 'b) nu" unfolding Nu_Share_def by simp
lemma K_rew: "(\<lambda>x. c) =  (K c)" by auto
lemma [simp]: "\<nu>Equalable N (\<lambda>x. c) = \<nu>Equalable N (K c)" by (auto simp add: K_rew)
lemma [simp]: "Nu_Share N s (\<lambda>z x. x) = Nu_Share N s (K id)" by (auto simp add: K_rew id_def)
lemma [\<nu>disposable]: "\<nu>Disposable T" for T :: "('a::naive_lrep) set" unfolding \<nu>Disposable_def by simp

  section\<open>Structures for construction\<close>

subsection \<open>Auxiliary tags\<close>

ML_val \<open>Term.dest_Type @{typ unit}\<close>
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

definition ParamTag :: " 'a \<Rightarrow> prop" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 10) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> Trueprop True"
lemma ParamTag_E: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" unfolding ParamTag_def using TrueI .
  \<comment>\<open>A tag used to indicate a parameter should be specified during application. It retains the order of the parameters to be specified.
  For example, "@{prop "\<And>bit_width value. \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_width \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> P bit_wdith value"},
    the first parameter `?bit_width` will be specified first and then the "?value".\<close>

subsection \<open>Register and its collection\<close>

datatype void = void \<comment>\<open> End of the stack \<close>
declare void.split[split]
definition Void :: "void set" where "Void = {void}" 
text \<open>The name `void` coincides that, when a procedure has no input arguments,
  the \<nu>-type for the input would exactly be @{term Void}. \<close>
lemma [simp,intro]: "void \<in> Void" unfolding Void_def by simp
lemma [simp,intro]: "Inhabited Void" unfolding Inhabited_def by auto
translations "a" <= "a \<^bold>a\<^bold>n\<^bold>d CONST Void"

datatype 'a register = Register name_tag 'a
  \<comment>\<open> Register label value
    where `label` is a free variable representing name of the register by its variable name\<close>
syntax "_register_as_" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a register" ("\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r _ \<^bold>a\<^bold>s _" [5,5] 4)
translations "_register_as_ name exp" == "CONST Register (NAME name) exp"
declare register.split[split]
definition get_register :: " 'a register \<Rightarrow> 'a" where "get_register r = (case r of (Register _ x) \<Rightarrow> x)"
definition map_register :: " ('a \<Rightarrow> 'b) \<Rightarrow> 'a register \<Rightarrow> 'b register "
  where "map_register f r = (case r of (Register name x) \<Rightarrow> Register name (f x))"

definition RegisterTy :: "name_tag \<Rightarrow> 'a set \<Rightarrow> 'a register set" where
  RegisterTy_def: "RegisterTy name s = {r. case r of Register name' x \<Rightarrow> name' = name \<and> x \<in> s}"
syntax "_register_set_" :: "idt \<Rightarrow> 'a set \<Rightarrow> 'a register set" ("\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r _ = _" [5,5] 4)
translations "_register_set_ name S" == "CONST RegisterTy (NAME name) S"
lemma [simp]: "Register v x \<in> RegisterTy v' T \<longleftrightarrow> v = v' \<and> x \<in> T" unfolding RegisterTy_def by simp
lemma [intro]: "x \<in> T \<Longrightarrow> Register name x \<in> RegisterTy name T" by simp
lemma [elim]: "r \<in> RegisterTy name T \<Longrightarrow> (\<And>x. r = Register name x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases r) simp
lemma [intro]: "Inhabited T \<Longrightarrow> Inhabited (RegisterTy name T)" unfolding Inhabited_def by auto
lemma [dest]: "Inhabited (RegisterTy name T) \<Longrightarrow> Inhabited T" unfolding Inhabited_def by auto

definition And :: " 'a \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b " (infixr "and'_pair" 3)  where [simp]:"And = Pair"
definition AndTy :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set " (infixr "and'_ty" 3)  where  "AndTy = (\<times>)"
translations
  "a \<^bold>a\<^bold>n\<^bold>d b" <= "a and_pair b"
  "a \<^bold>a\<^bold>n\<^bold>d b" <= "a and_ty b"
lemma [simp]: "(a, b) \<in> (A and_ty B) \<longleftrightarrow> a \<in> A \<and> b \<in> B" unfolding AndTy_def And_def by simp
lemma [intro]: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> (a, b) \<in> (A and_ty B)" by simp
lemma [elim]: "ab \<in> (A and_ty B) \<Longrightarrow> (\<And>a b. ab = (a, b) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding AndTy_def And_def by (cases ab) simp
lemma [intro]: "Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> Inhabited (A and_ty B)" unfolding Inhabited_def AndTy_def And_def by auto
lemma [elim]: "Inhabited (A and_ty B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

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
definition "disposable_prod = disposable \<times> disposable"
lemma [simp]: "(a,b) \<in> disposable \<longleftrightarrow> a \<in> disposable \<and> b \<in> disposable" unfolding disposable_prod_def by simp
instance by standard
end

instantiation prod :: (register_collection,register_collection) register_collection begin instance by standard end

subsection \<open>Stack structure\<close>

definition Stack_Delimiter :: " ('a :: lrep) set \<Rightarrow> ('b :: lrep) set \<Rightarrow> ('a \<times> 'b :: lrep) set " ( "_\<boxbar>_" [14,13] 13)
  where "Stack_Delimiter = (\<times>)"
definition End_of_Contextual_Stack :: " 'a \<Rightarrow> 'a " where "End_of_Contextual_Stack x = x" \<comment> \<open>A tag for printing sugar\<close>
translations "a" <= "a \<boxbar> CONST End_of_Contextual_Stack x" \<comment> \<open>hide the end\<close>
lemma [simp]: "(a,b) \<in> (A \<boxbar> B) \<longleftrightarrow> a \<in> A \<and> b \<in> B" unfolding Stack_Delimiter_def by simp
lemma Stack_Delimiter_I[intro]: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> (a,b) \<in> (A\<boxbar>B)" by simp
lemma Stack_Delimiter_E[elim]: "ab \<in> (A\<boxbar>B) \<Longrightarrow> (\<And>a b. ab = (a,b) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Stack_Delimiter_def by (cases ab) simp
lemma [intro]: "Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> Inhabited (U\<boxbar>V)" unfolding Inhabited_def by auto
lemma [elim]: "Inhabited (U\<boxbar>V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> PROP C) \<Longrightarrow> PROP C" unfolding Inhabited_def by auto

subsection \<open>Procedure construction context.\<close>

datatype ('a, 'r) "proc_ctx"  = Proc_Ctx 'a 'r
declare proc_ctx.split[split]
type_notation "proc_ctx" ("_/ \<flower> _" [2,2] 1)
definition Proc_CtxTy :: " ('a::lrep) set \<Rightarrow> ('b::register_collection) set \<Rightarrow> ('a \<flower> 'b) set" (infix "\<flower>" 2) \<comment> \<open>the flower operator\<close>
  where "Proc_CtxTy s t = {x. case x of Proc_Ctx a b \<Rightarrow> a \<in>s \<and> b \<in> t}"
    \<comment> \<open>The font of the flower operator is not specified, since any flower is a flower.\<close>
notation Proc_CtxTy ("(2\<flower_L>\<medium_left_bracket>//_//\<flower_L>\<flower>\<flower_R>//_//\<medium_right_bracket>\<flower_R>)" [2,2] 1000)  \<comment> \<open>Better decoration for better attention. It is the center of the construction.\<close>
(* two syntax sugars, defined as constants rather than syntax objects in order to merely enable definition-jumping by `Ctrl-Click`. *)
consts Proc_Ctx_NoRegisters :: 'a ("\<^bold>n\<^bold>o \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r\<^bold>s")
consts Proc_Ctx_EmptyStack :: 'a ("\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k")
translations "x \<flower> \<^bold>n\<^bold>o \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r\<^bold>s" == "x \<flower> CONST Void"
  "\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k \<flower> x" <= "CONST End_of_Contextual_Stack s \<flower> x"

lemma [simp]: "(Proc_Ctx s r) \<in> (T \<flower> U) \<equiv> s \<in> T \<and> r \<in> U" by (simp add: Proc_CtxTy_def)
lemma [\<nu>elim]: "c \<in> (T \<flower> U) \<Longrightarrow> (\<And>s r. c = (Proc_Ctx s r) \<Longrightarrow> s \<in> T \<Longrightarrow> r \<in> U \<Longrightarrow> C) \<Longrightarrow> C" by (cases c) auto
lemma Proc_CtxTy_intro[intro]: "s \<in> T \<Longrightarrow> r \<in> U \<Longrightarrow> Proc_Ctx s r \<in> (T \<flower> U)" by (simp add: Proc_CtxTy_def)
lemma [intro]: "Inhabited T \<Longrightarrow> Inhabited U \<Longrightarrow> Inhabited (T \<flower> U)" unfolding Inhabited_def by auto
lemma [elim]: "Inhabited (T \<flower> U) \<Longrightarrow> (Inhabited T \<Longrightarrow> Inhabited U \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (auto elim: \<nu>elim)

subsection \<open>The \<nu>-system VM and Procedure construction structures\<close>


datatype 'a state = StatOn 'a | STrap | SNeg
text\<open> The basic state of the \<nu>-system virtual machine is represented by type @{typ "'a state"}.
  The valid state @{term "StatOn p"} essentially has two major form, one without registers and another one with them,
      \<^item> @{term "StatOn (x1, x2, \<cdots>, xn, void)"},
      \<^item> @{term "StatOn (Proc_Ctx (x1, x2, \<cdots>, xn, void ) (\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r r1 \<^bold>a\<^bold>s y1 and_pair \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r r2 \<^bold>a\<^bold>s y2 and_pair \<cdots>))"},
  where @{term "(x1, x2, \<cdots>, xn, void)"} represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
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
lemma [elim]: "s \<in> \<S_S> T \<Longrightarrow> (\<And>x. s = StatOn x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma [intro]: "x \<in> T \<Longrightarrow> StatOn x \<in> \<S_S> T" by simp
lemma [elim]: "s \<in> \<S> T \<Longrightarrow> (\<And>x. s = StatOn x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> (s = SNeg \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma [intro]: "x \<in> T \<Longrightarrow> StatOn x \<in> \<S> T" and [intro]: "SNeg \<in> \<S> T" by simp_all
lemma LooseStateTy_upgrade: "s \<in> \<S> T \<Longrightarrow> s \<noteq> SNeg \<Longrightarrow> s \<in> \<S_S> T" by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> \<S_S> T \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> SNeg \<Longrightarrow> s \<in> \<S_S> T) \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma [intro]: "Inhabited (\<S> T)" unfolding Inhabited_def by auto
lemma [intro]: "Inhabited T \<Longrightarrow> Inhabited (\<S_S> T)" unfolding Inhabited_def by auto
lemma [dest]: "Inhabited (\<S_S> T) \<Longrightarrow> Inhabited T" unfolding Inhabited_def by (auto)

definition Procedure :: "('a \<Rightarrow> 'b state) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ \<blangle>(2 _/  \<longmapsto>  _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]:"Procedure f T U \<longleftrightarrow> (\<forall>a. a \<in> T \<longrightarrow> f a \<in> \<S> U)"
definition Map :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set " (infix "\<mapsto>" 60) where "A \<mapsto> B = {f. \<forall>a. a \<in> A \<longrightarrow> f a \<in> B }"
abbreviation Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<blangle>(2 _/ \<longmapsto> _ )\<brangle>)" [101,2,2] 100)
  where "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle> \<equiv> f \<in> T \<mapsto> U"
lemma [\<nu>def]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> A\<longmapsto> B\<brangle> \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> f a \<in> B)" unfolding Map_def by auto
lemma [intro]: "(\<And>x. x \<in> T \<Longrightarrow> f x \<in> U) \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle>" unfolding \<nu>def by auto
lemma [simp]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> \<S> U \<brangle> \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> T \<longmapsto> U \<brangle>" unfolding \<nu>def by fast 

subsection \<open>Primitive operations and instructions required in the system\<close>

subsubsection \<open>Elementary instructions\<close>

definition bind :: " 'a state \<Rightarrow> ('a \<Rightarrow> 'b state) \<Rightarrow> 'b state " \<comment>\<open>monadic bind\<close>
  where "bind s f = (case s of StatOn x \<Rightarrow> f x | STrap \<Rightarrow> STrap | SNeg \<Rightarrow> SNeg)"
definition instr_comp :: "('a \<Rightarrow> 'b state) \<Rightarrow> ('b \<Rightarrow> 'c state) \<Rightarrow> 'a \<Rightarrow> 'c state"  (infixr "\<nuInstrComp>" 75) 
  where "instr_comp f g s = bind (f s) g" \<comment>\<open>It is NOT monadic `then` operator (\<then>)!\<close>
definition nop :: " 'a \<Rightarrow> 'a state" where "nop = StatOn" \<comment>\<open>the instruction `no-operation`\<close>
definition call :: "('a \<Rightarrow> 'b state) \<Rightarrow> ('a \<flower> 'r) \<Rightarrow> ('b \<flower> 'r) state"
  where "call f s = (case s of Proc_Ctx x r \<Rightarrow> bind (f x) (\<lambda>x. StatOn (Proc_Ctx x r)))"
definition begin_proc_ctx :: " 'a \<Rightarrow> ('a \<flower> void) state" where "begin_proc_ctx x = StatOn (Proc_Ctx x void)"
definition end_proc_ctx :: " 'a \<flower> 'b \<Rightarrow> 'a state" where "end_proc_ctx ctx = (case ctx of Proc_Ctx x y \<Rightarrow> StatOn x)"

lemma nop: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> T \<longmapsto> T \<brangle>" unfolding nop_def Procedure_def by auto
lemma call: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c call f \<blangle> U \<flower> W \<longmapsto> V \<flower> W \<brangle>"
  unfolding call_def Procedure_def by  (auto simp add: bind_def)
lemma end_proc_ctx: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c end_proc_ctx \<blangle> T \<flower> R \<longmapsto> T \<brangle>" unfolding Procedure_def end_proc_ctx_def by auto

subsubsection \<open>Addressing\<close>

text \<open>Addresses provide the function to access and map the addressed part in a nested structure (e.g. a nested pair @{term "(a,((b,c),d))"}.
  It is achieved by nested composition of address functions. For example "get_at (address_L (address_R address_here))"
  returns @{term b} for the pattern @{term "((a,b),c)"}, and "map_at (address_L (address_R address_here)) f"
  maps a @{term "((a,b),c)"} to @{term "((a, f b),c)"}\<close>
datatype ('a,'b,'x,'y) address = Address "'a \<Rightarrow> 'x" "('x \<Rightarrow> 'y) \<Rightarrow> 'a \<Rightarrow> 'b"
declare  address.split[split]
declare \<nu>def[\<nu>address_def]
definition [\<nu>address_def]: "get_at adr = (case adr of Address g m \<Rightarrow> g)" \<comment> \<open>to access the addressed part\<close>
definition [\<nu>address_def]: "map_at adr = (case adr of Address g m \<Rightarrow> m)" 
definition address_here :: "('a,'b,'a,'b) address" where "address_here = Address id id"
definition address_left :: "('a,'b,'x,'y) address \<Rightarrow> ('a \<times> 'r, 'b \<times> 'r, 'x, 'y) address"
  where "address_left adr = (case adr of Address g m \<Rightarrow> Address (g \<circ> fst) (\<lambda>f x. case x of (l,r) \<Rightarrow> (m f l, r)))"
definition address_right :: "('a,'b,'x,'y) address \<Rightarrow> ('l \<times> 'a, 'l \<times> 'b, 'x, 'y) address"
  where "address_right adr = (case adr of Address g m \<Rightarrow> Address (g \<circ> snd) (\<lambda>f x. case x of (l,r) \<Rightarrow> (l, m f r)))"
definition AdrGet :: " ('a,'b,'x,'y) address \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> bool" ("(2\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s _/ \<blangle> _ \<^bold>@ _ \<brangle>)" [101,4,4] 100)
  where [\<nu>address_def]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> X \<^bold>@ A \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_at adr \<blangle> A \<longmapsto> X \<brangle>"
definition AdrMap :: " ('a,'b,'x,'y) address \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> 'y set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s _/ \<blangle> _ \<^bold>@ _ \<longmapsto> _ \<^bold>@ _ \<brangle>)" [101,4,4,4,4] 100)
  where [\<nu>address_def]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_at adr \<blangle> A \<longmapsto> X \<brangle> \<and> \<^bold>m\<^bold>a\<^bold>p map_at adr \<blangle> X \<mapsto> Y \<longmapsto> A \<mapsto> B \<brangle>"
lemma address_here_getter[\<nu>address_getter]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>address_def  address_here_def by auto
lemma address_here_mapper[\<nu>address_mapper]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>address_def  address_here_def by auto
lemma address_left_getter[\<nu>address_getter]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_left f \<blangle> X \<^bold>@ (A and_ty R) \<brangle>"
  unfolding \<nu>address_def address_left_def by (cases f) auto
lemma address_right_getter[\<nu>address_getter]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_right f \<blangle> X \<^bold>@ (L and_ty A) \<brangle>"
  unfolding \<nu>address_def address_right_def by (cases f) auto
lemma address_left_mapper[\<nu>address_mapper]:
    "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_left f \<blangle> X \<^bold>@ (A and_ty R) \<longmapsto> Y \<^bold>@ (B and_ty R) \<brangle>"
  unfolding \<nu>address_def address_left_def by (cases f) auto
lemma address_right_mapper[\<nu>address_mapper]:
    "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_right f \<blangle> X \<^bold>@ (L and_ty A) \<longmapsto> Y \<^bold>@ (L and_ty B) \<brangle>"
  unfolding \<nu>address_def address_right_def by (cases f) auto

subsubsection \<open>Register operations\<close>

definition new_reg_0 :: "('x \<times> 'R \<flower> void) \<Rightarrow> ('R \<flower> 'x register) state"
  where "new_reg_0 s = (case s of Proc_Ctx (x,R) void \<Rightarrow> StatOn (Proc_Ctx R (Register (NAME _) x)))"
definition new_reg_L :: "('G, 'G2, 't, 'x register \<times> 't) address \<Rightarrow> ('x \<times> 'R \<flower> 'G) \<Rightarrow> ('R \<flower> 'G2) state"
  where "new_reg_L adr s = (case s of Proc_Ctx (x,R) G \<Rightarrow> StatOn (Proc_Ctx R (map_at adr (\<lambda>t. (Register (NAME _) x,t)) G)))"
definition new_reg_R :: "('G, 'G2, 't, 't \<times> 'x register) address \<Rightarrow> ('x \<times> 'R \<flower> 'G) \<Rightarrow> ('R \<flower> 'G2) state"
  where "new_reg_R adr s = (case s of Proc_Ctx (x,R) G \<Rightarrow> StatOn (Proc_Ctx R (map_at adr (\<lambda>t. (t, Register (NAME _) x)) G)))"
definition store_reg :: "('G, 'G2, ('x::lrep) register, 'y register) address \<Rightarrow> ('y \<times> 'R \<flower> 'G) \<Rightarrow> ('R \<flower> 'G2) state"
  where "store_reg adr s = (case s of Proc_Ctx (x,r) G \<Rightarrow>
    if get_register (get_at adr G) \<in> disposable then  StatOn (Proc_Ctx r (map_at adr (map_register (K  x)) G)) else STrap)"
definition load_reg :: " ('a, 'a, ('x :: sharable_lrep) register, 'x register) address \<Rightarrow> 's \<flower> 'a \<Rightarrow> ('x \<times> 's \<flower> 'a) state"
  where "load_reg adr a = (case a of Proc_Ctx s rr \<Rightarrow>
    if  get_register (get_at adr rr) \<in> shareable then
      StatOn (Proc_Ctx (share (Gi 1) (get_register (get_at adr rr)), s) (map_at adr (map_register (share (Gi 1))) rr))
    else STrap)"
definition remove_reg :: "  ('R, 'R2, 'x register \<times> 'Z, 'Z) address \<Rightarrow> ('S \<flower> 'R) \<Rightarrow> ('x \<times> 'S \<flower> 'R2) state"
  where "remove_reg adr s = (case s of Proc_Ctx S R \<Rightarrow>
    StatOn (Proc_Ctx (get_register (fst (get_at adr R)), S) (map_at adr snd R)))"

lemma new_reg_0: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg_0 \<blangle> X\<boxbar>R \<flower> Void \<longmapsto> R \<flower> \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r \<n>\<a>\<m>\<e> = X \<brangle>" unfolding \<nu>address_def new_reg_0_def by auto
lemma new_reg_L:"\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> T \<^bold>@ G \<longmapsto> (\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r \<n>\<a>\<m>\<e> = X and_ty T) \<^bold>@ G2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg_L adr \<blangle> X\<boxbar>R \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def new_reg_L_def by auto
lemma new_reg_R:"\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> T \<^bold>@ G \<longmapsto> (T and_ty \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r \<n>\<a>\<m>\<e> = X) \<^bold>@ G2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg_R adr \<blangle> X\<boxbar>R \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def new_reg_R_def by auto
lemma store_reg: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> RegisterTy name X \<^bold>@ G \<longmapsto> RegisterTy name Y \<^bold>@ G2 \<brangle> \<Longrightarrow> \<nu>Disposable X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c store_reg adr \<blangle> Y\<boxbar>R \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def store_reg_def get_register_def map_register_def by auto
lemma load_reg: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> RegisterTy name (x \<tycolon> X) \<^bold>@ A \<longmapsto> RegisterTy name (sh (Gi 1) x \<tycolon> X) \<^bold>@ B \<brangle>
  \<Longrightarrow> Nu_Share X s sh \<Longrightarrow> x \<in> s \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c load_reg adr \<blangle> R \<flower> A \<longmapsto> sh (Gi 1) x \<tycolon>  X\<boxbar>R \<flower> B \<brangle>"
  unfolding \<nu>address_def load_reg_def Nu_Share_def get_register_def map_register_def by auto
lemma remove_reg: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> (RegisterTy name X and_ty Z) \<^bold>@ V \<longmapsto> Z \<^bold>@ V' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c remove_reg adr \<blangle> R \<flower> V \<longmapsto> X\<boxbar>R \<flower> V' \<brangle>"
  unfolding \<nu>address_def remove_reg_def get_register_def by (auto split: prod.split simp add: fst_def)



schematic_goal "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_right (address_left (address_left (address_here))) \<blangle> ?X \<^bold>@ ?A \<brangle>" by (rule \<nu>address_getter)+
schematic_goal th1: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s (?adr::('a \<times> 'b \<times> 'c,?'z, 'b, ?'x) address) \<blangle> X \<^bold>@ (A and_ty X and_ty C) \<longmapsto> ?Y \<^bold>@ ?Z \<brangle>" 
  including show_more by (rule \<nu>address_mapper)+

ML_val \<open>
val tm2 = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_schematic @{context}) "(\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s (?adr::('a \<times> 'b \<times>'b1\<times> 'b2\<times> 'c,?'z, 'c, ?'x) address) \<blangle> C \<^bold>@ (A and_ty X and_ty X2 and_ty X3 and_ty C) \<longmapsto> ?Y \<^bold>@ ?Z \<brangle>)"
  |> Thm.cterm_of @{context}
val tm = Thm.cprop_of @{thm th1}
val th = Goal.init tm2
val th2 = Tactical.SOLVED' (Tactical.REPEAT o Tactic.resolve_tac @{context} @{thms \<nu>address_mapper}) 1 th |> Seq.hd
\<close>

  subsection \<open>Top-level constructions\<close>

definition CurrentConstruction :: " 'a state \<Rightarrow> 'a set \<Rightarrow> bool " ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,11] 10)
  where "CurrentConstruction s S \<longleftrightarrow> s \<in> \<S_S> S"
definition PendingConstruction :: " ('a \<Rightarrow> 'b state) \<Rightarrow> 'a state \<Rightarrow> 'b set \<Rightarrow> bool " ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,5] 4)
  where "PendingConstruction f s S \<longleftrightarrow> bind s f \<in> \<S> S"

definition CodeBlock :: " 'a state \<Rightarrow> 'b => 'b set \<Rightarrow> ('b \<Rightarrow> 'a state) \<Rightarrow> bool" where
  CodeBlock_def: "CodeBlock stat arg ty prog \<longleftrightarrow> (arg \<in> ty \<and> prog arg = stat \<and> stat \<noteq> SNeg)"
syntax "_codeblock_exp_" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> bool"  ("(2\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _/  \<^bold>a\<^bold>s '\<open>_'\<close>/ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>)" [100,0,0] 3)
syntax "_codeblock_" :: "idt \<Rightarrow> logic \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>" [100,0] 3)
syntax "_codeblock_noarg_" :: "idt \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>w\<^bold>i\<^bold>t\<^bold>h\<^bold>o\<^bold>u\<^bold>t \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t" [100] 3)
translations "_codeblock_ v ty" <= "CONST CodeBlock v arg ty exp"
  "_codeblock_noarg_ v" <= "_codeblock_ v (CONST End_of_Contextual_Stack x)"
(* translations "_codeblock_exp_ v exp ty" <= "CONST CodeBlock v arg ty exp" *)

definition Fact :: "name_tag \<Rightarrow> bool \<Rightarrow> prop" where "Fact label P \<equiv>Trueprop P"
syntax "Fact_sugar_" :: "idt \<Rightarrow> logic \<Rightarrow> prop" ("\<^item> _ : _" [5,0] 4)
translations "Fact_sugar_ name P" == "CONST Fact (NAME name) P"
lemma Fact_I: "P \<Longrightarrow> PROP Fact label P" unfolding Fact_def .
lemma Fact_D: "\<^item> name : P \<Longrightarrow> P" unfolding Fact_def .

definition NoFact :: "prop" ("\<^bold>n\<^bold>o\<^bold>t\<^bold>h\<^bold>i\<^bold>n\<^bold>g") where "NoFact \<equiv> Trueprop True"
lemma NoFact: "PROP NoFact" unfolding NoFact_def using TrueI .
definition AndFact :: "prop \<Rightarrow> prop \<Rightarrow> prop" (infixr "and'_fact" 3) where "AndFact \<equiv> (&&&)"
translations "_pretty_and_ P Q" <= "CONST AndFact P Q"
translations "_pretty_and_ P Q" <= "CONST AndFact P Q"
lemma AndFact_I: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP P and_fact PROP Q" unfolding AndFact_def using conjunctionI .
lemma AndFact_D1: "PROP P and_fact PROP Q \<Longrightarrow> PROP P" unfolding AndFact_def using conjunctionD1 .
lemma AndFact_D2: "PROP P and_fact PROP Q \<Longrightarrow> PROP Q" unfolding AndFact_def using conjunctionD2 .
definition Facts :: "bool \<Rightarrow> prop \<Rightarrow> prop" ("\<glowing_star> _/ \<^bold>a\<^bold>n\<^bold>d _" [4,3] 3)
  where "\<glowing_star> P \<^bold>a\<^bold>n\<^bold>d (PROP Q) \<equiv> (P &&& PROP Q)"
translations "Q" <= " CONST Facts (CONST True) Q"
lemma Facts_imp: " (\<glowing_star> P \<^bold>a\<^bold>n\<^bold>d (PROP Q) \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R)"
  unfolding Facts_def conjunction_imp by rule
lemma Facts_I: "P \<Longrightarrow> PROP Q \<Longrightarrow> \<glowing_star> P \<^bold>a\<^bold>n\<^bold>d (PROP Q)" unfolding Facts_def using conjunctionI .

definition SpecTop :: "prop \<Rightarrow> prop \<Rightarrow> prop" where SpecTop_def: "SpecTop \<equiv> (&&&)"
\<comment>\<open> SpecTop focus lemmata
  where the focus is the focused one or multiple HOL propositions intended to be constructed
    the lemmata are several propositions served as auxiliary facts, e.g. post conditions.\<close>
notation SpecTop ("SPEC'_TOP _ _")
  and SpecTop ("_/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s:/ _ " [1,1] 0)
lemma SpecTop_focus[dest]: "(PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<Longrightarrow> PROP P" unfolding SpecTop_def conjunction_imp .
lemma SpecTop_facts[dest]: "(PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<Longrightarrow> PROP L" unfolding SpecTop_def conjunction_imp .
lemma SpecTop_imp: "(PROP SpecTop (PROP P) (PROP L) \<Longrightarrow> PROP C) \<equiv> (PROP P \<Longrightarrow> PROP L \<Longrightarrow> PROP C)"
  unfolding SpecTop_def conjunction_imp .
lemma SpecTop_I: "PROP P \<Longrightarrow> PROP L \<Longrightarrow> PROP SpecTop (PROP P) (PROP L)" unfolding SpecTop_def using conjunctionI .
(* lemma Specification_rule_focus: "(P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP Q) \<Longrightarrow> (PROP Q \<Longrightarrow> P \<Longrightarrow> P') \<Longrightarrow> (P' \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP Q)"
    unfolding SpecTop_def by presburger
lemma Specification_rule_aux: "(P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: Q) \<Longrightarrow> (Q \<Longrightarrow> Q') \<Longrightarrow> (P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: Q')"
    unfolding SpecTop_def  by presburger *)

section \<open>Principal rules\<close>

theorem apply_proc: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp by auto

theorem  accept_proc: "\<medium_left_bracket> \<And>s. CodeBlock s a S f \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L ) \<medium_right_bracket> \<Longrightarrow>
  \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m s' \<Longrightarrow> CodeBlock s' a S (f \<nuInstrComp> g) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: (PROP L))" for L :: "prop"
  unfolding PropBlock_def CodeBlock_def instr_comp_def CurrentConstruction_def PendingConstruction_def
proof (rule SpecTop_I)
  assume a: "(\<And>s. a \<in> S \<and> f a = s \<and> s \<noteq> SNeg \<Longrightarrow> SPEC_TOP (bind s g \<in> \<S> T) (PROP L))" and b: " a \<in> S \<and> bind (f a) g = s' \<and> s' \<noteq> SNeg"
  from b have sa: "a \<in> S \<and> f a = f a \<and> f a \<noteq> SNeg" by (cases "f a") (auto simp add: bind_def)
  note th = a[OF sa, simplified b[THEN conjunct1]]
  from th[THEN SpecTop_focus] show "s' \<in> \<S_S> T" using b by (blast intro: LooseStateTy_upgrade)
  from th[THEN SpecTop_facts] show "PROP L" .
qed

theorem start_construction: "CodeBlock s a S begin_proc_ctx \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (S \<flower> Void) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: (PROP NoFact))"
  for S :: " ('a::lrep) set" and a :: 'a and s :: "('a \<flower> void) state" including show_more1
  unfolding begin_proc_ctx_def CodeBlock_def CurrentConstruction_def by (rule SpecTop_I; (rule NoFact)?) auto

theorem finish_construction: "\<medium_left_bracket>\<And>a s. CodeBlock s a S f \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (T \<flower> R) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L \<medium_right_bracket>
  \<Longrightarrow> f' = f \<nuInstrComp> end_proc_ctx \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> S \<longmapsto> T \<brangle>"
    unfolding PropBlock_def CodeBlock_def Procedure_def
proof
  assume rule:"(\<And>a s. a \<in> S \<and> f a = s \<and> s \<noteq> SNeg \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (T \<flower> R) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)"
    and def: "f' = f \<nuInstrComp> end_proc_ctx"
  fix a show "a \<in> S \<longrightarrow> f' a \<in> \<S> T " unfolding def proof
    assume a: "a \<in> S"
    moreover note rule[of a "f a", unfolded CurrentConstruction_def, simplified, THEN SpecTop_focus] 
    ultimately show "(f \<nuInstrComp> end_proc_ctx) a \<in> \<S> T" unfolding instr_comp_def bind_def end_proc_ctx_def
      using LooseStateTy_introByStrict by (cases "f a") auto
  qed
qed

lemma conj_imp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)" by rule simp+
lemma  y: "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<and> Q \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: \<glowing_star> P \<^bold>a\<^bold>n\<^bold>d PROP L) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: \<glowing_star> Q \<^bold>a\<^bold>n\<^bold>d PROP L)"
  unfolding SpecTop_imp conj_imp Facts_imp by (intro SpecTop_I Facts_I)
lemma name_star_fact: "(P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: \<glowing_star> Q \<^bold>a\<^bold>n\<^bold>d PROP L) \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m name \<Longrightarrow> (P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: \<glowing_star> True \<^bold>a\<^bold>n\<^bold>d \<^item> name : Q and_fact PROP L)"
  unfolding SpecTop_imp Facts_imp by (intro SpecTop_I Facts_I TrueI Fact_I AndFact_I)

  section \<open>Supplementary structures for elementary functions\<close>

definition ExTyp :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" (binder "\<exists>* " 10) where "ExTyp T = {x. (\<exists>z. x \<in> T z)}"
  \<comment> \<open>which represents there exists some images (or rarely abstractors) subject to the typing.
    And then the image subjecting the typing could be fixed as a local variable by the \<nu>-obtain command. \<close>
lemma [simp]: "x \<in> ExTyp T \<equiv> (\<exists>z. x \<in> T z)" unfolding ExTyp_def by auto
lemma [simp]: "\<S_S> (ExTyp T) = (\<exists>* x. \<S_S> (T x))" unfolding ExTyp_def by auto
lemma [simp]: "\<S> (ExTyp T) = (\<exists>* x. \<S> (T x))" unfolding ExTyp_def by auto
lemma [simp]: "(ExTyp T \<boxbar> R) = (\<exists>*x. (T x \<boxbar> R))" and "(S \<boxbar> ExTyp T) = (\<exists>*x. (S \<boxbar> T x))" unfolding ExTyp_def by auto
lemma [simp]: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ExTyp T) \<longleftrightarrow> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)" unfolding CurrentConstruction_def by simp

definition AddtionTy :: " 'a set \<Rightarrow> bool \<Rightarrow> 'a set " (infixl "\<addtion>" 50) where " T \<addtion> P = {x. x \<in> T \<and> P}"
lemma [simp]: "s \<in> \<S_S> (T \<addtion> P) \<longleftrightarrow> s \<in> \<S_S> T \<and> P" unfolding AddtionTy_def by (cases s) simp_all
lemma [simp]: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<addtion> P) \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P" unfolding CurrentConstruction_def by simp
lemma [simp]: "((((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<and> B) \<and> C) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<equiv> (((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<and> (B \<and> C)) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)" by simp

definition Cast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _/ \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o _)" [2,2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P) \<longleftrightarrow> (Inhabited A \<longrightarrow> A \<subseteq> B \<and> P)"
abbreviation SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<equiv> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o True)"
lemma Inhabited_subset: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Inhabited B" unfolding Inhabited_def by auto
lemma CastE[elim]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Cast_def by (auto intro: Inhabited_subset)
lemma CastI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P" unfolding Cast_def by auto
lemma [\<nu>cast]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" by blast
lemma [\<nu>cast]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t \<S_S> A \<longmapsto> \<S_S> B \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P" by blast
lemma [\<nu>cast]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P2 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<boxbar>B) \<longmapsto> (A'\<boxbar>B') \<^bold>a\<^bold>n\<^bold>d\<^bold>a\<^bold>l\<^bold>s\<^bold>o P1 \<and> P2" by blast

  section \<open>Finalize the syntax sugars to be ready for use\<close>
no_translations "_pretty_and_ P Q" <= "CONST AndFact P Q"
translations "_linebreak_collection_ P Q" <= "CONST AndFact P Q"

end
