(* KEEP IT SIMPLE AND STUPID *)

theory NuPrim \<comment> \<open>The Primary Theory of the \<nu>-System\<close>
  imports Main "HOL-Library.Monad_Syntax" NuHelpMath
  abbrevs "is" = "\<^bold>i\<^bold>s"
      and "as" = "\<^bold>a\<^bold>s"
      and "register" = "\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r"
      and "in" = "\<^bold>i\<^bold>n"
      and "with" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
      and "auxiliary_facts" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "auxfacts" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "<proc>" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
      and "<map>" = "\<^bold>m\<^bold>a\<^bold>p"
      and "<param>" = "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m"
      and ",," = "\<heavy_comma>"
      and "<cast>" = "\<^bold>c\<^bold>a\<^bold>s\<^bold>t"
      and "<meanwhile>" = "\<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e"
      and address = "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s"
      and "<conversion>" = "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n"
      and "<auto>" = "\<^bold>a\<^bold>u\<^bold>t\<^bold>o"
      and "<premise>" = "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e"
      and atomic = "\<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c"
      and construct = "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t"
      and "by" = "\<^bold>b\<^bold>y"
      and "simplify" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y"
      and "<END>" = "\<^bold>E\<^bold>N\<^bold>D"
begin

text \<open>The fundamental theory for \<nu>-system\<close>

section Preliminary

ML_file NuConfig.ML
bundle show_more1 = [[show_hyps = true, show_types = true, show_sorts = true]]
bundle show_more = [[show_hyps = true, show_types = true]]

named_theorems \<nu>intro "\<nu>-type introduction rules" and \<nu>intro' and \<nu>intro0 and \<nu>elim "\<nu>-type elimination rules"
  \<comment> \<open>\<nu> introduction and elimination rules destructs and reconstructs \<nu> typings.
    They are not required in the program construction,
    and generally it is not expected to destruct \<nu> typings during the construction.
    Therefore, they are not included in the standard introduction and elimination rules.
    However they are quite useful in primitive proofs for properties (e.g. cast) and instructions. \<close>
named_theorems \<nu>def \<open>primitive definitions used to unfold in proofs of primitive instructions.\<close>
  and \<nu>address_def \<open>primitive definitions for unfolding in proofs for address\<close>
  and \<nu>post_construct and \<nu>auto_destruct
named_theorems typing_expn "expansion theorems for abstractions"

subsection \<open>Syntax and Notations\<close>

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
(* translations
  "a \<^bold>a\<^bold>n\<^bold>d b \<^bold>a\<^bold>n\<^bold>d c" <= "(a \<^bold>a\<^bold>n\<^bold>d b) \<^bold>a\<^bold>n\<^bold>d c"
  "_linebreak_collection_ a (_linebreak_collection_ b c)" <= "_linebreak_collection_ (_linebreak_collection_ a b) c" *)
text \<open> `_pretty_and_` suppresses parentheses in the printing. For example, both the term
  "1 and 2 and 3" and  "(1 and 2) and 3" are printed identically, as "1 and 2 and 3". 
  It is useful to represent a collection of object which has some complicated inner structure
    (e.g. a binary tree) that is not intended to be displayed to user.\<close>

subsection \<open>Preliminary data structures and Auxiliary definition\<close>

definition K_def[simp]: "K a b = a"
lemma K_intro[intro]: "(\<forall>x y. f x y = x) \<Longrightarrow> f = K" by (simp add: ext)

definition ProtectorI :: "'a \<Rightarrow> 'a" where "ProtectorI x = x"
lemma [cong]: "ProtectorI X \<equiv> ProtectorI X" .

definition WorkingProtector :: "'a \<Rightarrow> 'a" where "WorkingProtector x \<equiv> x"

datatype 'a tree = Leaf | Node 'a \<open>'a tree\<close> \<open>'a tree\<close>

subsubsection \<open>Structures assembling propositions\<close>

definition NoFact :: "prop" ("\<^bold>n\<^bold>o\<^bold>t\<^bold>h\<^bold>i\<^bold>n\<^bold>g") where "NoFact \<equiv> Trueprop True"
lemma NoFact: "PROP NoFact" unfolding NoFact_def using TrueI .
definition AndFact :: "prop \<Rightarrow> prop \<Rightarrow> prop" (infixr "and'_fact" 3) where "AndFact \<equiv> (&&&)"
translations "P" <= "CONST AndFact P (CONST NoFact)"
translations "_pretty_and_ P Q" <= "CONST AndFact P Q"
lemma AndFact_I: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP P and_fact PROP Q" unfolding AndFact_def using conjunctionI .
lemma AndFact_D1: "PROP P and_fact PROP Q \<Longrightarrow> PROP P" unfolding AndFact_def using conjunctionD1 .
lemma AndFact_D2: "PROP P and_fact PROP Q \<Longrightarrow> PROP Q" unfolding AndFact_def using conjunctionD2 .

(* definition FactTree :: "prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop"
  where "FactTree (PROP X) (PROP L) (PROP R) \<equiv> (PROP X &&& PROP L &&& PROP R)"
lemma FactTree_imp: "(PROP FactTree (PROP X) (PROP L) (PROP R) \<Longrightarrow> PROP C) \<equiv> (PROP X \<Longrightarrow> PROP L \<Longrightarrow> PROP R \<Longrightarrow> PROP C)"
  unfolding FactTree_def conjunction_imp .
lemma FactTree_X: "PROP FactTree (PROP X) (PROP L) (PROP R) \<Longrightarrow> PROP X" unfolding FactTree_imp .
lemma FactTree_L: "PROP FactTree (PROP X) (PROP L) (PROP R) \<Longrightarrow> PROP L" unfolding FactTree_imp .
lemma FactTree_R: "PROP FactTree (PROP X) (PROP L) (PROP R) \<Longrightarrow> PROP R" unfolding FactTree_imp .
lemma FactTree_I: "PROP X \<Longrightarrow> PROP L \<Longrightarrow> PROP R \<Longrightarrow> PROP FactTree (PROP X) (PROP L) (PROP R)"
  unfolding FactTree_def by (intro conjunctionI)
translations "_pretty_and_ L (_pretty_and_ X R)" <= "CONST FactTree X L R" *)

subsubsection \<open>The type representing ownership\<close>

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

lemma [simp]:  "Gi n + Gi m = Gi (n + m)"  by (simp add: plus_zint_def)
lemma [simp]:  "Gz + x = Gz" by (simp add: plus_zint_def)
lemma [simp]:  "x + Gz = Gz" by (cases x,auto simp add: plus_zint_def)
lemma [simp]: "x + Gi 0 = x" and [simp]: "Gi 0 + x = x" by (cases x; auto)+

instance by standard ((simp add: plus_zint_def split: zint.splits)+)
end  

section\<open>Low representation for semantics\<close>

subsection\<open>LRep: Low Representation for semantics\<close>

text \<open>The semantic framework follows a style of shallow embedding, where semantics for different type (e.g. integers, floats)
  are modelled by different Isabelle type. Model types are constrained by the base type class {\it lrep} and types representing
  objects that supports certain features are constrained by specific sub-classes which extend the base class {\it lrep} finally. \<close>

datatype llty = la_i nat \<comment> \<open>int bits\<close> | la_p nat \<comment> \<open>pointer space\<close> | la_tup llty | la_array llty nat | la_z | la_C llty llty
  \<comment> \<open>LLVM types representing integers in specified bit length, pointers in the given space, structures of given content
  (usually a list by @{term la_C}), arrays of given content and fixed length, abstract type filtered during code extraction,
  and the list constructor which is used in argument list and structure's filed list,  respectively. \<close>

class disposable =
  fixes disposable :: " 'a \<Rightarrow> bool " \<comment> \<open>Whether a value could be thrown away freely\<close>

class lrep = disposable + \<comment>\<open>The basic class for types modelling concrete objects\<close>
  fixes llty :: "'a itself \<Rightarrow> llty" \<comment> \<open>The LLVM type to which the model type corresponds\<close>

syntax "_LLTY_" :: "type \<Rightarrow> logic" ("LLTY'[_']")
translations  "LLTY['x]" == "CONST llty TYPE('x)"

class ceq =  \<comment> \<open>equality comparison\<close>
  fixes ceqable :: " 'a \<Rightarrow> 'a \<Rightarrow> bool" \<comment> \<open>Whether two values could be compared for equality\<close>
  fixes ceq :: " 'a \<Rightarrow> 'a \<Rightarrow> bool" \<comment> \<open>The equality of two values.
    It is only valid when the two values could be compared, that the @{term ceqable} for them is true.\<close>
  assumes ceqable_sym[simp]: "ceqable x y = ceqable y x"
  assumes ceq_refl[intro]: "ceqable x x \<Longrightarrow> ceq x x"
  assumes ceq_sym[simp]: "ceqable x y \<Longrightarrow> ceq x y \<longleftrightarrow> ceq y x"
  assumes ceq_trans: "ceqable x y \<Longrightarrow> ceqable y z \<Longrightarrow> ceqable x z
    \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z"

datatype ownership = OWS_1 zint | OWS_0 | OWS_C ownership ownership | OWS_L "ownership list"

definition owns_prod :: " ('a \<Rightarrow> ownership) \<Rightarrow> ('b \<Rightarrow> ownership) \<Rightarrow> ('a \<times> 'b \<Rightarrow> ownership) " (infixl "\<times>\<^sub>o\<^sub>w" 80)
  where "owns_prod ow1 ow2 = (\<lambda>(a,b). OWS_C (ow1 a) (ow2 b))"
lemma [simp]: "owns_prod ow1 ow2 (a,b) = OWS_C (ow1 a) (ow2 b)"
  unfolding owns_prod_def by simp

class ownership =
  fixes ownership :: " 'a \<Rightarrow> ownership"

class sharing_identical =
  fixes sharing_identical :: " 'a \<Rightarrow> 'a \<Rightarrow> bool "
  assumes sharing_identical_refl[simp]: "sharing_identical x x"
  assumes sharing_identical_sym[simp]: "sharing_identical x y \<longleftrightarrow> sharing_identical y x"
  assumes sharing_identical_trans: "sharing_identical x y \<Longrightarrow> sharing_identical y z \<Longrightarrow> sharing_identical x z"

class share =
  \<comment> \<open>for objects whose the ownership can be shared \<close>
  fixes shareable :: "'a \<Rightarrow> bool" \<comment> \<open>Whether the ownership of a value could be shared.
      It is a predicate giving the precise control to decide on the shareability for each value.\<close>
    and share :: "zint \<Rightarrow> 'a \<Rightarrow> 'a"
    and dpriv :: "'a \<Rightarrow> 'a"
  assumes share_id[simp]: "share (Gi 0) x = x"
  assumes share_assoc[simp]: "share b (share a x) = share (a + b) x"


class naive_lrep = share + sharing_identical + lrep +
  assumes [simp]: "disposable x = True"
  assumes [simp]: "shareable x = True"
  assumes [simp]: "dpriv x = x"
  assumes [simp]: "share z x = x"
  assumes [simp]: "sharing_identical x y = True"  

subsection \<open>The \<nu>-type\<close>

subsubsection \<open>Definitions\<close>

type_synonym ('a,'b) nu = " 'a \<Rightarrow> 'b \<Rightarrow> bool "
datatype ('a::lrep,'b) typing = typing 'b "('a,'b) nu" (infix "\<tycolon>" 15) \<comment>\<open>shortcut keys "<ty>"\<close>
primrec nu_of :: "('a::lrep,'b) typing \<Rightarrow> ('a,'b) nu" where "nu_of (x \<tycolon> N) = N"
primrec image_of :: "('a::lrep,'b) typing \<Rightarrow> 'b" where "image_of (x \<tycolon> N) = x"

definition RepSet :: "('a::lrep,'b) typing \<Rightarrow> 'a set" ("\<tort_lbrace> _ \<tort_rbrace>") where "\<tort_lbrace> ty \<tort_rbrace> = {p. case ty of (x \<tycolon> R) \<Rightarrow> R p x }"
abbreviation Refining :: "('a::lrep) \<Rightarrow> ('a,'b) nu \<Rightarrow> 'b \<Rightarrow> bool" ("(_/ \<nuLinkL> _ \<nuLinkR>/ _)" [27,15,27] 26) \<comment>\<open>shortcut keys "--<" and ">--"\<close>
  where  "(p \<nuLinkL> N \<nuLinkR> x) \<equiv> p \<in> \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
definition Inhabited :: " 'a set \<Rightarrow> bool" where "Inhabited s \<equiv> (\<exists>x. x \<in> s)"
abbreviation InhabitTyp :: " 'b \<Rightarrow> ('a::lrep,'b) nu \<Rightarrow> bool" (infix "\<ratio>" 15)  \<comment>\<open>shortcut keys ":TY:"\<close>
  where  "(x \<ratio> N) \<equiv> Inhabited \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
text \<open>The @{term "x \<tycolon> N"} is a predication specifying concrete values,
  e.g. @{prop "a_concrete_int32 \<in> \<tort_lbrace>(42::nat) \<tycolon> N 32\<tort_rbrace> "} and also @{prop "state \<in> State (\<tort_lbrace>42 \<tycolon> N\<tort_rbrace> \<times> \<tort_lbrace>24 \<tycolon> N\<tort_rbrace> \<times> \<cdots> )"}.
  It constitutes basic elements in specification.
  The @{prop "p \<nuLinkL> N \<nuLinkR> x"} as the abbreviation of $p \<in> (x \<tycolon> N)$ is an abstraction between concrete value @{term p} and
  abstracted {\it image} @{term x} via the \<nu>-{\it abstractor} @{term N} which defines the abstraction relationship itself.
  The next @{prop "x \<ratio> N"} is a proposition stating @{term x} is an image of abstractor @{term N} and therefore
  the \<nu>-type @{term "x \<tycolon> N"} is inhabited. Basically it is used to derive implicated conditions of images,
  e.g. @{prop "(42 \<ratio> N 32) \<Longrightarrow> 42 < 2^32"}\<close>

subsubsection \<open>Rudimentary lemmata\<close>

lemma Refining_ex: "p \<nuLinkL> R \<nuLinkR> x \<equiv> R p x" unfolding RepSet_def by simp
lemma inhabited[dest]: "p \<nuLinkL> N \<nuLinkR> x \<Longrightarrow> x \<ratio> N" unfolding Inhabited_def by auto
lemma [elim!,\<nu>elim]: "Inhabited (U \<times> V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> PROP C) \<Longrightarrow> PROP C" unfolding Inhabited_def by auto
lemma [intro]: "x \<in> S \<Longrightarrow> Inhabited S" unfolding Inhabited_def by auto
lemma Inhabited_E: "Inhabited S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

subsubsection \<open>Properties\<close>

definition \<nu>Zero :: "('a::{zero,lrep},'b) nu \<Rightarrow> 'b \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Zero N x \<longleftrightarrow> 0 \<nuLinkL> N \<nuLinkR> x"
definition \<nu>Share :: "('a::{share,lrep},'b) nu \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> (zint \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool"
  where "\<nu>Share N P f \<longleftrightarrow> (\<forall>z p x. P x \<and>(p \<nuLinkL> N \<nuLinkR> x) \<longrightarrow> shareable p \<and> (share z p \<nuLinkL> N \<nuLinkR> f z x))"
definition \<nu>Deprive :: "('a::{share,lrep},'b) nu \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Deprive N dp \<longleftrightarrow> (\<forall>p x. (p \<nuLinkL> N \<nuLinkR> x) \<longrightarrow> dpriv p \<nuLinkL> N \<nuLinkR> dp x)"
definition \<nu>CEqual :: "('a::{ceq,lrep}, 'b) nu \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>CEqual N P eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2. P x1 x2 \<and> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> N \<nuLinkR> x2) \<longrightarrow> ceqable p1 p2 \<and> (ceq p1 p2 = eq x1 x2))"
definition \<nu>Disposable :: " ('a::lrep) set \<Rightarrow> bool " where [\<nu>def]: "\<nu>Disposable T \<longleftrightarrow> (\<forall>x. x \<in> T \<longrightarrow> disposable x)"
definition \<nu>ShrIdentical :: " ('a::{sharing_identical,lrep}, 'b) nu \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>ShrIdentical N sid \<longleftrightarrow> (\<forall>p1 p2 x1 x2. sid x1 x2 \<and> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> N \<nuLinkR> x2) \<longrightarrow> sharing_identical p1 p2)"
definition \<nu>Ownership :: " ('a::{ownership,lrep}, 'b) nu \<Rightarrow> ('b \<Rightarrow> ownership) \<Rightarrow> bool "
  where [\<nu>def]: "\<nu>Ownership N ow \<longleftrightarrow> (\<forall>p x. (p \<nuLinkL> N \<nuLinkR> x) \<longrightarrow> ownership p = ow x)"

lemma [\<nu>intro]: "\<nu>Share N (\<lambda>x. True) (\<lambda>z x. x)" for N :: "('a::naive_lrep, 'b) nu" unfolding \<nu>Share_def by simp
lemma [\<nu>intro]: "\<nu>Deprive N id" for N :: "('a::naive_lrep, 'b) nu" unfolding \<nu>Deprive_def by simp
(* lemma K_rew: "(\<lambda>x. c) =  (K c)" by auto
lemma [simp]: "\<nu>CEqual N (\<lambda>x. c) = \<nu>CEqual N (\<lambda>x. c)" by (auto simp add: K_rew)
lemma [simp]: "\<nu>Share N s (\<lambda>z x. x) = \<nu>Share N s (K id)" by (auto simp add: K_rew id_def) *)
lemma [\<nu>intro]: "\<nu>Disposable T" for T :: "('a::naive_lrep) set" unfolding \<nu>Disposable_def by simp
lemma [\<nu>intro]: "\<nu>ShrIdentical N (\<lambda>x y. True)" for N :: "('a::naive_lrep, 'b) nu" unfolding \<nu>ShrIdentical_def by simp

lemma [elim]: "\<nu>Share N P sh \<Longrightarrow> ((P x \<Longrightarrow> p \<nuLinkL> N \<nuLinkR> x \<Longrightarrow> shareable p) \<Longrightarrow> (P x \<Longrightarrow> p \<nuLinkL> N \<nuLinkR> x \<Longrightarrow> share z p \<nuLinkL> N \<nuLinkR> sh z x) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding \<nu>Share_def by simp

  section\<open>Structures for construction\<close>

subsection \<open>Auxiliary tags\<close>

subsubsection \<open>Name tag\<close>

ML_val \<open>Term.dest_Type @{typ unit}\<close>
datatype name_tag = NAME_TAG "unit \<Rightarrow> unit"
datatype name2_tag = NAME2_TAG "unit \<Rightarrow> unit \<Rightarrow> unit"
lemma [cong]: "NAME_TAG x \<equiv> NAME_TAG x" and [cong]: "NAME2_TAG y \<equiv> NAME2_TAG y" using reflexive .
syntax "_NAME_" :: "idt \<Rightarrow> name_tag" ("NAME _" [0] 1000)
  "_NAME2_" :: "idt => idt => name_tag" ("NAME2 _ _" [0,0] 1000)
translations "NAME name" == "CONST NAME_TAG (\<lambda>name. ())"
  "NAME2 name1 name2" == "CONST NAME2_TAG (\<lambda>name1 name2. ())"
lemma name_tag_eq: "x = y" for x :: name_tag by (cases x, cases y) auto

definition Named :: "name_tag \<Rightarrow> 'a \<Rightarrow> 'a" where "Named name x = x" \<comment>\<open>name tag\<close>
syntax "_named_" :: "logic \<Rightarrow> idt \<Rightarrow> logic" (infix "named" 14)
translations "x named name" == "CONST Named (NAME name) x"
ML_val \<open> Syntax.read_term @{context} "AAA named yy" \<close>

subsubsection \<open>Parameter tag\<close>

definition ParamTag :: " 'a \<Rightarrow> prop" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 10) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> Trueprop True"
lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
  \<comment>\<open>A tag used to indicate a parameter should be specified during application. It retains the order of the parameters to be specified.
  For example, "@{prop "\<And>bit_width value. \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_width \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> P bit_wdith value"},
    the first parameter `?bit_width` will be specified first and then the "?value".\<close>
lemma [elim!,\<nu>elim]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" by auto

definition ParamHOL :: " 'a \<Rightarrow> bool" where "ParamHOL x = True"
lemma ParamHOL: "Trueprop (ParamHOL x) \<equiv> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" unfolding ParamTag_def ParamHOL_def .

subsubsection \<open>Premise tag\<close>

definition Premise :: "bool \<Rightarrow> prop" ("\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e _" [10] 9) where [\<nu>def]:"Premise \<equiv> Trueprop"
  \<comment> \<open>A tag to hint automatic provers to try to prove this proof obligation\<close>
lemma Premise_I: "P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P" unfolding Premise_def by simp
lemma Premise_E: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> P" unfolding Premise_def by simp
lemma [elim!,\<nu>elim]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> C" unfolding Premise_def by simp
lemma Premise_Irew: "(P \<Longrightarrow> PROP C) \<equiv> (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> PROP C)" unfolding Premise_def by simp

definition PremiseHOL :: "bool \<Rightarrow> bool" where "PremiseHOL x = x"
lemma PremiseHOL: "Trueprop (PremiseHOL P) \<equiv> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P" unfolding Premise_def PremiseHOL_def .

(* attribute_setup intro_premise = \<open>
  Scan.succeed (Thm.rule_attribute [] (fn _ => fn th => th COMP @{thm Premise_I}))
\<close>*)
attribute_setup elim_premise = \<open>
  Scan.succeed (Thm.rule_attribute [] (fn _ => fn th => th COMP @{thm Premise_E}))
\<close>

subsubsection \<open>Simplify tag\<close>

definition Simplify :: "'a \<Rightarrow> 'a \<Rightarrow> prop" ("\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y _ : _" [100,10] 9) 
  where "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y x : y \<equiv> (x \<equiv> y)"
lemma Simplify_I: "y \<equiv> x \<Longrightarrow> \<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y x : y" unfolding Simplify_def .

subsection \<open>Register and its collection\<close>

datatype void = void \<comment>\<open> End of the stack \<close>
declare void.split[split]
definition Void :: "void set" where "Void = {void}" 
text \<open>The name `void` coincides that, when a procedure has no input arguments,
  the \<nu>-type for the input would exactly be @{term Void}. \<close>
lemma [simp,intro]: "void \<in> Void" unfolding Void_def by simp
lemma [simp,intro]: "Inhabited Void" unfolding Inhabited_def by auto
lemma [elim!, \<nu>elim]: "Inhabited Void \<Longrightarrow> C \<Longrightarrow> C" .
(*translations "a" <= "a \<^bold>a\<^bold>n\<^bold>d CONST Void"*)

datatype 'a register = Register name_tag "'a::lrep"
  \<comment>\<open> Register label value
    where `label` is a free variable representing name of the register by its variable name\<close>
syntax "_register_as_" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a register" ("\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r _ \<^bold>a\<^bold>s _" [5,5] 4)
translations "_register_as_ name exp" == "CONST Register (NAME name) exp"
declare register.split[split]
definition get_register :: " ('a::lrep) register \<Rightarrow> 'a" where "get_register r = (case r of (Register _ x) \<Rightarrow> x)"
definition map_register :: " ('a \<Rightarrow> 'b) \<Rightarrow> ('a::lrep) register \<Rightarrow> ('b::lrep) register "
  where "map_register f r = (case r of (Register name x) \<Rightarrow> Register name (f x))"

class register_collection = lrep
  \<comment> \<open><^class>\<open>local_registers\<close> is a binary tree organizing registers in a certain code block.
    \<^class>\<open>register_collection\<close> is a binary tree organizing \^class>\<open>local_registers\<close> to form contextual registers in a construction.
    A register_collection is always a lrep, but a lrep may not a register collection.
    register_collection ::= void | register_local local_registers | register_collection \<times> register_collection.
    local_registers ::= void | register | register \<times> register. \<close>

instantiation void :: lrep begin
definition llty_void :: "void itself \<Rightarrow> llty" where [simp]: "llty_void _ = la_z"
definition disposable_void :: "void \<Rightarrow> bool" where [simp]: "disposable_void x = True"
instance by standard
end

instantiation register :: (lrep) register_collection begin
definition llty_register :: "'a register itself \<Rightarrow> llty" where [simp]: "llty_register _ = la_z"
definition disposable_register :: "'a register \<Rightarrow> bool"
  where disposable_register: "disposable_register = pred_register disposable"
instance by standard
end

instantiation prod :: (disposable,disposable) disposable begin
definition "disposable_prod = disposable \<times>\<^sub>p disposable"
lemma [simp]: "disposable (a,b) \<longleftrightarrow> disposable a \<and> disposable b" unfolding disposable_prod_def by simp
instance by standard
end

instantiation prod :: (lrep,lrep) lrep begin
definition llty_prod :: "('a \<times> 'b) itself \<Rightarrow> llty" where [simp]: "llty_prod _ = la_C (llty TYPE('a)) (llty TYPE('b))"
instance by standard
end

instantiation void :: register_collection begin instance by standard end
instantiation prod :: (register_collection,register_collection) register_collection begin instance by standard end

definition RegisterTy :: "name_tag \<Rightarrow> ('a::lrep) set \<Rightarrow> 'a register set" where
  RegisterTy_def: "RegisterTy name s = {r. case r of Register name' x \<Rightarrow> name' = name \<and> x \<in> s}"
syntax "_register_set_" :: "idt \<Rightarrow> 'a set \<Rightarrow> 'a register set" ("\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r _ = _" [5,5] 4)
translations "_register_set_ name S" == "CONST RegisterTy (NAME name) S"
translations "S" <= "CONST RegisterTy (NAME name) \<tort_lbrace>S\<tort_rbrace>"
lemma [simp]: "Register v x \<in> RegisterTy v' T \<longleftrightarrow> v = v' \<and> x \<in> T" unfolding RegisterTy_def by simp
lemma [intro]: "x \<in> T \<Longrightarrow> Register name x \<in> RegisterTy name T" by simp
lemma [elim]: "r \<in> RegisterTy name T \<Longrightarrow> (\<And>x. r = Register name x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases r) simp
lemma [intro]: "Inhabited T \<Longrightarrow> Inhabited (RegisterTy name T)" unfolding Inhabited_def by auto
lemma [elim!]: "Inhabited (RegisterTy name T) \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "\<nu>Disposable x \<Longrightarrow> \<nu>Disposable (RegisterTy name x)" unfolding \<nu>Disposable_def
  including show_more1 by (auto simp add: disposable_register)

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
lemma [elim!,\<nu>elim]: "Inhabited (A and_ty B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto
lemma [\<nu>intro]: "\<nu>Disposable A \<Longrightarrow> \<nu>Disposable B \<Longrightarrow> \<nu>Disposable (A and_ty B)"
  unfolding \<nu>Disposable_def by auto

subsection \<open>Stack structure\<close>

class stack = lrep
instantiation void :: stack begin instance by standard end
instantiation prod :: (lrep,stack) stack begin instance by standard end

definition Stack_Delimiter :: " ('a :: stack) set \<Rightarrow> ('b :: lrep) set \<Rightarrow> ('b \<times> 'a) set " ( "(2_/ \<heavy_comma> _)" [13,14] 13)
  where "Stack_Delimiter a b = (b \<times> a)"
definition End_of_Stack ("\<^bold>E\<^bold>N\<^bold>D") where "End_of_Stack = Void"
definition End_of_Contextual_Stack :: " 'a \<Rightarrow> 'a " where "End_of_Contextual_Stack x = x" \<comment> \<open>A tag for printing sugar\<close>
translations "a" <= "CONST End_of_Contextual_Stack x \<heavy_comma> a" \<comment> \<open>hide the end\<close>
  "a" <= "CONST End_of_Stack\<heavy_comma> a"
translations "R \<heavy_comma> x \<tycolon> N" == "R \<heavy_comma> \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
lemma [elim,\<nu>elim]: "Inhabited (End_of_Contextual_Stack S) \<Longrightarrow> C \<Longrightarrow> C" .
lemma [simp]: "(a,b) \<in> (B \<heavy_comma> A) \<longleftrightarrow> a \<in> A \<and> b \<in> B" unfolding Stack_Delimiter_def by simp
lemma Stack_Delimiter_I[intro]: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> (a,b) \<in> (B \<heavy_comma> A)" by simp
lemma Stack_Delimiter_E[elim]: "ab \<in> (B \<heavy_comma> A) \<Longrightarrow> (\<And>a b. ab = (a,b) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> C) \<Longrightarrow> C" unfolding Stack_Delimiter_def by (cases ab) simp
lemma [simp]: "Inhabited (U\<heavy_comma>V) \<longleftrightarrow> Inhabited U \<and> Inhabited V" unfolding Inhabited_def by auto
lemma [intro]: "Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> Inhabited (U\<heavy_comma>V)" unfolding Inhabited_def by auto
lemma [elim!,\<nu>elim]: "Inhabited (U\<heavy_comma>V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> PROP C) \<Longrightarrow> PROP C" unfolding Inhabited_def by auto

subsection \<open>Procedure construction context.\<close>

datatype ('a, 'r) "proc_ctx" ("_/ \<flower> _" [2,2] 1)  = Proc_Ctx "('a::lrep)" "('r::register_collection)"
declare proc_ctx.split[split]
definition Proc_CtxTy :: " ('a::lrep) set \<Rightarrow> ('b::register_collection) set \<Rightarrow> ('a \<flower> 'b) set" (infix "\<flower>" 2) \<comment> \<open>the flower operator\<close>
  where "Proc_CtxTy s t = { Proc_Ctx a b | a b. a \<in>s \<and> b \<in> t}"
    \<comment> \<open>The font of the flower operator is not specified, since any flower is a flower.\<close>
notation Proc_CtxTy ("\<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k\<^bold>: _ \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r\<^bold>s _" [2,2] 1000)  \<comment> \<open>Better decoration for better attention. It is the center of the construction.\<close>
(* two syntax sugars, defined as constants rather than syntax objects in order to merely enable definition-jumping by `Ctrl-Click`. *)
consts Proc_Ctx_NoRegisters :: ind ("\<^bold>n\<^bold>o \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r\<^bold>s")
consts Proc_Ctx_EmptyStack :: ind ("\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k")
translations "x \<flower> \<^bold>n\<^bold>o \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r\<^bold>s" == "x \<flower> CONST Void"
  "\<^bold>e\<^bold>m\<^bold>p\<^bold>t\<^bold>y \<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k" <= "CONST End_of_Contextual_Stack s"
lemma [elim]: "c \<in> (X \<flower> G) \<Longrightarrow> (\<And>x g. c = Proc_Ctx x g \<Longrightarrow> x \<in> X \<Longrightarrow> g \<in> G \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Proc_CtxTy_def by (cases c) auto
lemma [intro]: "x \<in> X \<Longrightarrow> g \<in> G \<Longrightarrow> Proc_Ctx x g \<in> (X \<flower> G)" unfolding Proc_CtxTy_def by auto
lemma [simp]: "Inhabited (X \<flower> G) \<longleftrightarrow> Inhabited X \<and> Inhabited G"
  unfolding Proc_CtxTy_def Inhabited_def by auto
lemma [elim!,\<nu>elim]: "Inhabited (X \<flower> G) \<Longrightarrow> (Inhabited X \<Longrightarrow> Inhabited G \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Proc_CtxTy_def Inhabited_def by auto
lemma [intro]: "Inhabited X \<Longrightarrow> Inhabited G \<Longrightarrow> Inhabited (X \<flower> G)"
  unfolding Proc_CtxTy_def Inhabited_def by auto

instantiation proc_ctx :: (lrep,register_collection) lrep begin
definition llty_proc_ctx :: "('a,'b) proc_ctx itself \<Rightarrow> llty" where "llty_proc_ctx _ = la_C (llty TYPE('a)) (llty TYPE('b))"
definition disposable_proc_ctx :: "('a,'b) proc_ctx \<Rightarrow> bool" where "disposable_proc_ctx x = False"
instance by standard
end

lemma [simp]: "(Proc_Ctx s r) \<in> (T \<flower> U) \<equiv> s \<in> T \<and> r \<in> U" by (simp add: Proc_CtxTy_def)
lemma [\<nu>elim]: "c \<in> (T \<flower> U) \<Longrightarrow> (\<And>s r. c = (Proc_Ctx s r) \<Longrightarrow> s \<in> T \<Longrightarrow> r \<in> U \<Longrightarrow> C) \<Longrightarrow> C" by (cases c) auto
lemma Proc_CtxTy_intro[intro]: "s \<in> T \<Longrightarrow> r \<in> U \<Longrightarrow> Proc_Ctx s r \<in> (T \<flower> U)" by (simp add: Proc_CtxTy_def)
lemma [intro]: "Inhabited T \<Longrightarrow> Inhabited U \<Longrightarrow> Inhabited (T \<flower> U)" unfolding Inhabited_def by auto
lemma [elim!,\<nu>elim]: "Inhabited (T \<flower> U) \<Longrightarrow> (Inhabited T \<Longrightarrow> Inhabited U \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (auto elim: \<nu>elim)

subsection \<open>The \<nu>-system VM and Procedure construction structures\<close>

datatype 'a state = StatOn "('a::lrep)" | STrap | SNeg
text\<open> The basic state of the \<nu>-system virtual machine is represented by type @{typ "('a::lrep) state"}.
  The valid state @{term "StatOn p"} essentially has two major form, one without registers and another one with them,
      \<^item> @{term "StatOn (x1, x2, \<cdots>, xn, void)"},
      \<^item> @{term "StatOn (Proc_Ctx (x1, x2, \<cdots>, xn, void ) (register_local (\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r r1 \<^bold>a\<^bold>s y1 and_pair \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r r2 \<^bold>a\<^bold>s y2 and_pair \<cdots>)))"},
  where @{term "(x1, x2, \<cdots>, xn, void)"} represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term SNeg} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term SNeg} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>
declare state.split[split]
definition StrictStateTy :: " ('a::lrep) set \<Rightarrow> 'a state set" ("\<S_S> _" [56] 55)
  where "\<S_S> T = {s. case s of StatOn x \<Rightarrow> x \<in> T | STrap \<Rightarrow> False | SNeg \<Rightarrow> False}"
definition LooseStateTy :: " ('a::lrep) set \<Rightarrow> 'a state set" ("\<S> _" [56] 55)
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

definition Procedure :: "('a \<Rightarrow> 'b state) \<Rightarrow> ('a::lrep) set \<Rightarrow> ('b::lrep) set \<Rightarrow> bool" ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ \<blangle>(2 _/  \<longmapsto>  _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]:"Procedure f T U \<longleftrightarrow> (\<forall>a. a \<in> T \<longrightarrow> f a \<in> \<S> U)"
definition Map :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set " (infix "\<mapsto>" 60) where "A \<mapsto> B = {f. \<forall>a. a \<in> A \<longrightarrow> f a \<in> B }"
abbreviation Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<blangle>(2 _/ \<longmapsto> _ )\<brangle>)" [101,2,2] 100)
  where "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle> \<equiv> f \<in> T \<mapsto> U"
lemma [\<nu>def]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> A\<longmapsto> B\<brangle> \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> f a \<in> B)" unfolding Map_def by auto
lemma [intro]: "(\<And>x. x \<in> T \<Longrightarrow> f x \<in> U) \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle>" unfolding \<nu>def by auto
lemma [simp]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> \<S> U \<brangle> \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> T \<longmapsto> U \<brangle>" unfolding \<nu>def by fast 

subsection \<open>Primitive operations and instructions required in the system\<close>

subsubsection \<open>Elementary instructions\<close>

definition bind :: " ('a::lrep) state \<Rightarrow> ('a \<Rightarrow> 'b state) \<Rightarrow> ('b::lrep) state " \<comment>\<open>monadic bind\<close>
  where "bind s f = (case s of StatOn x \<Rightarrow> f x | STrap \<Rightarrow> STrap | SNeg \<Rightarrow> SNeg)"
definition instr_comp :: "(('a::lrep) \<Rightarrow> ('b::lrep) state) \<Rightarrow> ('b \<Rightarrow> ('c::lrep) state) \<Rightarrow> 'a \<Rightarrow> 'c state"  ("_ \<nuInstrComp>/ _" [75,76] 75) 
  where "instr_comp f g s = bind (f s) g" \<comment>\<open>It is NOT monadic `then` operator (\<then>)!\<close>
definition nop :: " ('a::lrep) \<Rightarrow> 'a state" where "nop = StatOn" \<comment>\<open>the instruction `no-operation`\<close>
definition call :: "(('a::lrep) \<Rightarrow> ('b::lrep) state) \<Rightarrow> ('a \<flower> ('r::register_collection)) \<Rightarrow> ('b \<flower> 'r) state"
  where "call f s = (case s of Proc_Ctx x r \<Rightarrow> bind (f x) (\<lambda>x. StatOn (Proc_Ctx x r)))"
definition begin_proc_ctx :: " ('a::lrep) \<Rightarrow> ('a \<flower> void) state" where "begin_proc_ctx x = StatOn (Proc_Ctx x void)"
definition end_proc_ctx :: " ('a::lrep) \<flower> ('b::register_collection) \<Rightarrow> 'a state"
  where "end_proc_ctx ctx = (case ctx of Proc_Ctx x y \<Rightarrow> StatOn x)"

lemma nop_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> T \<longmapsto> T \<brangle>" unfolding nop_def Procedure_def by auto
lemma call[intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c call f \<blangle> U \<flower> W \<longmapsto> V \<flower> W \<brangle>"
  unfolding call_def Procedure_def by  (auto simp add: bind_def)
lemma begin_proc_ctx: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c begin_proc_ctx \<blangle> S \<longmapsto> S \<flower> Void \<brangle>" unfolding begin_proc_ctx_def \<nu>def by auto
lemma end_proc_ctx: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c end_proc_ctx \<blangle> T \<flower> R \<longmapsto> T \<brangle>" unfolding Procedure_def end_proc_ctx_def by auto
lemma instr_comp[intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> B \<longmapsto> C \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> g) \<blangle> A \<longmapsto> C \<brangle>"
  unfolding instr_comp_def Procedure_def bind_def by auto

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
  where "address_left adr = (case adr of Address g m \<Rightarrow> Address (g \<circ> fst) (apfst o m))"
definition address_right :: "('a,'b,'x,'y) address \<Rightarrow> ('l \<times> 'a, 'l \<times> 'b, 'x, 'y) address"
  where "address_right adr = (case adr of Address g m \<Rightarrow> Address (g \<circ> snd) (apsnd o m))"

definition AdrGet :: " ('a,'b,'x,'y) address \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> bool" ("(2\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s _/ \<blangle> _ \<^bold>@ _ \<brangle>)" [101,4,4] 100)
  where [\<nu>address_def]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> X \<^bold>@ A \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_at adr \<blangle> A \<longmapsto> X \<brangle>"
definition AdrMap :: " ('a,'b,'x,'y) address \<Rightarrow> 'x set \<Rightarrow> 'a set \<Rightarrow> 'y set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s _/ \<blangle> _ \<^bold>@ _ \<longmapsto> _ \<^bold>@ _ \<brangle>)" [101,4,4,4,4] 100)
  where [\<nu>address_def]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B \<brangle> \<longleftrightarrow> \<^bold>m\<^bold>a\<^bold>p get_at adr \<blangle> A \<longmapsto> X \<brangle> \<and> \<^bold>m\<^bold>a\<^bold>p map_at adr \<blangle> X \<mapsto> Y \<longmapsto> A \<mapsto> B \<brangle>"

lemma address_here_getter[\<nu>intro]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_here \<blangle> A \<^bold>@ A \<brangle>"
  unfolding \<nu>address_def  address_here_def by auto
lemma address_here_mapper[\<nu>intro]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_here \<blangle> A \<^bold>@ A \<longmapsto> B \<^bold>@ B \<brangle>"
  unfolding \<nu>address_def  address_here_def by auto
lemma address_left_getter[\<nu>intro]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_left f \<blangle> X \<^bold>@ (A and_ty R) \<brangle>"
  unfolding \<nu>address_def address_left_def by (cases f) auto
lemma address_right_getter[\<nu>intro]: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s f \<blangle> X \<^bold>@ A \<brangle> \<Longrightarrow> \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_right f \<blangle> X \<^bold>@ (L and_ty A) \<brangle>"
  unfolding \<nu>address_def address_right_def by (cases f) auto
lemma address_left_mapper[\<nu>intro]:
    "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_left f \<blangle> X \<^bold>@ (A and_ty R) \<longmapsto> Y \<^bold>@ (B and_ty R) \<brangle>"
  unfolding \<nu>address_def address_left_def by (cases f) auto
lemma address_right_mapper[\<nu>intro]:
    "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s f \<blangle> X \<^bold>@ A \<longmapsto> Y \<^bold>@ B\<brangle> \<Longrightarrow> \<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_right f \<blangle> X \<^bold>@ (L and_ty A) \<longmapsto> Y \<^bold>@ (L and_ty B) \<brangle>"
  unfolding \<nu>address_def address_right_def by (cases f) auto

subsubsection \<open>Register operations\<close>

(* definition new_reg_0 :: "(('x::lrep) \<times> ('R::lrep) \<flower> void) \<Rightarrow> ('R \<flower> 'x register) state"
  where "new_reg_0 s = (case s of Proc_Ctx (x,R) void \<Rightarrow> StatOn (Proc_Ctx R (Register (NAME _) x)))"
definition new_reg_L :: "('G, 'G2, 't, 'x register \<times> 't) address \<Rightarrow> (('x::lrep) \<times> ('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "new_reg_L adr s = (case s of Proc_Ctx (x,R) G \<Rightarrow> StatOn (Proc_Ctx R (map_at adr (\<lambda>t. (Register (NAME _) x,t)) G)))"
definition new_reg_R :: "('G, 'G2, 't, 't \<times> 'x register) address \<Rightarrow> (('x::lrep) \<times> ('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "new_reg_R adr s = (case s of Proc_Ctx (x,R) G \<Rightarrow> StatOn (Proc_Ctx R (map_at adr (\<lambda>t. (t, Register (NAME _) x)) G)))" *)
thm address_left_mapper
thm address_here_mapper

definition new_reg :: "('G, 'G2, ('r::register_collection), void register \<times> 'r) address \<Rightarrow> (('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "new_reg adr s = (case s of Proc_Ctx r G \<Rightarrow> StatOn (Proc_Ctx r (map_at adr (Pair (Register (NAME_TAG id) void)) G)))"
definition new_reg_locale :: "('G, 'G2, ('r::register_collection), void \<times> 'r) address \<Rightarrow> (('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "new_reg_locale adr s = (case s of Proc_Ctx r G \<Rightarrow> StatOn (Proc_Ctx r (map_at adr (Pair void) G)))"
definition delete_reg_locale :: "('G, 'G2, ('r::register_collection) \<times> ('B::register_collection), 'B) address \<Rightarrow> (('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "delete_reg_locale adr s = (case s of Proc_Ctx r G \<Rightarrow>
    if disposable (fst (get_at adr G)) then StatOn (Proc_Ctx r (map_at adr snd G)) else STrap)"

definition store_reg :: "('G, 'G2, ('x::lrep) register, 'y register) address \<Rightarrow> (('y::lrep) \<times> ('R::lrep) \<flower> ('G::register_collection)) \<Rightarrow> ('R \<flower> ('G2::register_collection)) state"
  where "store_reg adr s = (case s of Proc_Ctx (x,r) G \<Rightarrow>
    if disposable (get_register (get_at adr G)) then  StatOn (Proc_Ctx r (map_at adr (map_register (K  x)) G)) else STrap)"
definition load_reg :: " ('a, 'a, ('x :: {share, lrep}) register, 'x register) address \<Rightarrow> ('s::lrep) \<flower> ('a::register_collection) \<Rightarrow> ('x \<times> 's \<flower> 'a) state"
  where "load_reg adr a = (case a of Proc_Ctx s rr \<Rightarrow>
    if shareable (get_register (get_at adr rr)) then
      StatOn (Proc_Ctx (share (Gi 1) (get_register (get_at adr rr)), s) (map_at adr (map_register (share (Gi 1))) rr))
    else STrap)"
definition remove_reg :: "  ('R, 'R2, 'x register, void register) address \<Rightarrow> (('S::lrep) \<flower> ('R::register_collection)) \<Rightarrow> (('x::lrep) \<times> 'S \<flower> ('R2::register_collection)) state"
  where "remove_reg adr s = (case s of Proc_Ctx S R \<Rightarrow>
    StatOn (Proc_Ctx (get_register (get_at adr R), S) (map_at adr (K (Register (NAME_TAG id) void)) R)))"

(* lemma new_reg_0: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg_0 \<blangle> X\<heavy_comma>R \<flower> Void \<longmapsto> R \<flower> \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r \<n>\<a>\<m>\<e> = X \<brangle>" unfolding \<nu>address_def new_reg_0_def by auto
lemma new_reg_L:"\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> T \<^bold>@ G \<longmapsto> (\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r \<n>\<a>\<m>\<e> = X and_ty T) \<^bold>@ G2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg_L adr \<blangle> X\<heavy_comma>R \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def new_reg_L_def by auto
lemma new_reg_R:"\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> T \<^bold>@ G \<longmapsto> (T and_ty \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r \<n>\<a>\<m>\<e> = X) \<^bold>@ G2 \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg_R adr \<blangle> X\<heavy_comma>R \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def new_reg_R_def by auto *)




lemma new_reg: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> W \<^bold>@ G \<longmapsto> (\<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r \<n>\<a>\<m>\<e> =  Void and_ty W) \<^bold>@ G2 \<brangle>
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg adr \<blangle> R \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def new_reg_def get_register_def map_register_def
  using name_tag_eq by (cases adr) auto

lemma new_reg_locale: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> W \<^bold>@ G \<longmapsto> (Void and_ty W) \<^bold>@ G2 \<brangle>
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c new_reg_locale adr \<blangle> R \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def new_reg_locale_def get_register_def map_register_def
  using name_tag_eq by (cases adr) auto

lemma delete_reg_locale: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> (W and_ty Z) \<^bold>@ G \<longmapsto> Z \<^bold>@ G2 \<brangle> \<Longrightarrow> \<nu>Disposable W
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c delete_reg_locale adr \<blangle> R \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def delete_reg_locale_def get_register_def map_register_def
  using name_tag_eq by (cases adr) (auto 4 3)

lemma store_reg: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> RegisterTy name X \<^bold>@ G \<longmapsto> RegisterTy name Y \<^bold>@ G2 \<brangle> \<Longrightarrow> \<nu>Disposable X \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c store_reg adr \<blangle> R \<heavy_comma> Y \<flower> G \<longmapsto> R \<flower> G2 \<brangle>"
  unfolding \<nu>address_def store_reg_def get_register_def map_register_def by auto
lemma load_reg: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> RegisterTy name \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>@ A \<longmapsto> RegisterTy name \<tort_lbrace>sh (Gi 1) x \<tycolon> X\<tort_rbrace> \<^bold>@ B \<brangle>
  \<Longrightarrow> \<nu>Share X s sh \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e s x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c load_reg adr \<blangle> R \<flower> A \<longmapsto> R \<heavy_comma> sh (Gi 1) x \<tycolon>  X \<flower> B \<brangle>"
  unfolding \<nu>address_def load_reg_def \<nu>Share_def get_register_def map_register_def by auto
lemma remove_reg: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s adr \<blangle> (RegisterTy name X) \<^bold>@ V \<longmapsto> (RegisterTy name Void) \<^bold>@ V' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c remove_reg adr \<blangle> R \<flower> V \<longmapsto> R \<heavy_comma> X \<flower> V' \<brangle>"
  unfolding \<nu>address_def remove_reg_def get_register_def using name_tag_eq by (auto split: prod.split simp add: fst_def)



schematic_goal "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s address_right (address_left (address_left (address_here))) \<blangle> ?X \<^bold>@ ?A \<brangle>" by (rule \<nu>intro)+
schematic_goal th1: "\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s (?adr::('a \<times> 'b \<times> 'c,?'z, 'b, ?'x) address) \<blangle> X \<^bold>@ (A and_ty X and_ty C) \<longmapsto> ?Y \<^bold>@ ?Z \<brangle>" 
  including show_more by (rule \<nu>intro)+

ML_val \<open>
val tm2 = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_schematic @{context}) "(\<^bold>a\<^bold>d\<^bold>d\<^bold>r\<^bold>e\<^bold>s\<^bold>s (?adr::('a \<times> 'b \<times>'b1\<times> 'b2\<times> 'c,?'z, 'c, ?'x) address) \<blangle> C \<^bold>@ (A and_ty X and_ty X2 and_ty X3 and_ty C) \<longmapsto> ?Y \<^bold>@ ?Z \<brangle>)"
  |> Thm.cterm_of @{context}
val tm = Thm.cprop_of @{thm th1}
val th = Goal.init tm2
val th2 = Tactical.SOLVED' (Tactical.REPEAT o Tactic.resolve_tac @{context} @{thms \<nu>intro}) 1 th |> Seq.hd
\<close>

  subsection \<open>Top-level constructions\<close>

definition CurrentConstruction :: " ('a::lrep) state \<Rightarrow> 'a set \<Rightarrow> bool " ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,11] 10)
  where "CurrentConstruction s S \<longleftrightarrow> s \<in> \<S_S> S"
definition PendingConstruction :: " (('a::lrep) \<Rightarrow> ('b::lrep) state) \<Rightarrow> 'a state \<Rightarrow> 'b set \<Rightarrow> bool " ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,5] 4)
  where "PendingConstruction f s S \<longleftrightarrow> bind s f \<in> \<S> S"

lemma [elim!,\<nu>elim]: "CurrentConstruction s S \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> C" unfolding CurrentConstruction_def by auto

definition CodeBlock :: " ('a::lrep) state \<Rightarrow> ('b::lrep) => 'b set \<Rightarrow> ('b \<Rightarrow> 'a state) \<Rightarrow> bool" where
  CodeBlock_def: "CodeBlock stat arg ty prog \<longleftrightarrow> (arg \<in> ty \<and> prog arg = stat \<and> stat \<noteq> SNeg)"
syntax "_codeblock_exp_" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> bool"  ("(2\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _/  \<^bold>a\<^bold>s '\<open>_'\<close>/ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>)" [100,0,0] 3)
syntax "_codeblock_noarg_exp_" :: "idt \<Rightarrow> logic \<Rightarrow> bool"  ("(2\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _/  \<^bold>a\<^bold>s '\<open>_'\<close>/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h\<^bold>o\<^bold>u\<^bold>t \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t)" [100,0] 3)
syntax "_codeblock_" :: "idt \<Rightarrow> logic \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>" [100,0] 3)
syntax "_codeblock_noarg_" :: "idt \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>w\<^bold>i\<^bold>t\<^bold>h\<^bold>o\<^bold>u\<^bold>t \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t" [100] 3)

attribute_setup show_codeblock_expression =  \<open>
  Scan.lift (Parse.$$$ "=" |-- ((Args.$$$ "false" >> K false) || (Args.$$$ "true" >> K true)) >>
    (Thm.declaration_attribute o K o Config.put_generic NuConfig.show_codeblock_expression))\<close>
print_translation \<open>
  let
    fun is_EoS (Const (\<^const_syntax>\<open>End_of_Contextual_Stack\<close>, _) $ _) = true
      | is_EoS tm = false
    fun codeblock_print ctx [v,arg,ty,exp] =
      if Config.get ctx NuConfig.show_codeblock_expression
      then if is_EoS ty
        then Syntax.const \<^syntax_const>\<open>_codeblock_noarg_exp_\<close> $ v $ exp
        else Syntax.const \<^syntax_const>\<open>_codeblock_exp_\<close> $ v $ ty $ exp
      else if is_EoS ty
        then Syntax.const \<^syntax_const>\<open>_codeblock_noarg_\<close> $ v
        else Syntax.const \<^syntax_const>\<open>_codeblock_\<close> $ v $ ty
  in
   [(\<^const_syntax>\<open>CodeBlock\<close>, codeblock_print)]
  end
\<close>

lemma [elim!,\<nu>elim]: "CodeBlock v arg ty prog \<Longrightarrow> (Inhabited ty \<Longrightarrow> C) \<Longrightarrow> C" unfolding CodeBlock_def by auto
lemma CodeBlock_unabbrev: "CodeBlock v arg ty prog \<Longrightarrow> (v \<equiv> ProtectorI (prog arg))"
  unfolding CodeBlock_def ProtectorI_def by (rule eq_reflection) fast
lemma CodeBlock_abbrev: "CodeBlock v arg ty prog \<Longrightarrow> ProtectorI (prog arg) \<equiv> v"
  unfolding CodeBlock_def ProtectorI_def by (rule eq_reflection) fast

definition Fact :: "name_tag \<Rightarrow> bool \<Rightarrow> prop" where "Fact label P \<equiv>Trueprop P"
syntax "Fact_sugar_" :: "idt \<Rightarrow> logic \<Rightarrow> prop" ("\<^item> _ : _" [5,0] 4)
translations "Fact_sugar_ name P" == "CONST Fact (NAME name) P"
lemma Fact_I: "P \<Longrightarrow> PROP Fact label P" unfolding Fact_def .
lemma Fact_D: "\<^item> name : P \<Longrightarrow> P" unfolding Fact_def .


definition FactCollection :: "prop \<Rightarrow> prop \<Rightarrow> prop \<Rightarrow> prop"
  where "FactCollection (PROP P) (PROP Q) (PROP S) \<equiv> (PROP P &&& PROP Q &&& PROP S)"
    \<comment> \<open>P: star fact, Q: fact list, S: \<nu>current\<close>
consts FactCollection_sugar :: "prop \<Rightarrow> prop \<Rightarrow> prop"  ("\<glowing_star> _/ \<^bold>a\<^bold>n\<^bold>d _" [4,3] 3)
translations
  "Q" <= " CONST FactCollection (CONST NoFact) Q S"
  "CONST FactCollection_sugar P Q" <= "CONST FactCollection P Q S"
lemma FactCollection_imp: " (PROP FactCollection (PROP P) (PROP Q) (PROP S) \<Longrightarrow> PROP R) \<equiv> (PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP S \<Longrightarrow> PROP R)"
  unfolding FactCollection_def conjunction_imp by rule
lemma FactCollection_I: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP S \<Longrightarrow> PROP  FactCollection (PROP P) (PROP Q) (PROP S)"
  unfolding FactCollection_def by (intro conjunctionI)
lemma FactCollection_D1: "PROP FactCollection (PROP P) (PROP Q) (PROP S) ==> PROP P" unfolding FactCollection_imp .
lemma FactCollection_D2: "PROP FactCollection (PROP P) (PROP Q) (PROP S) ==> PROP Q" unfolding FactCollection_imp .
lemma FactCollection_D3: "PROP FactCollection (PROP P) (PROP Q) (PROP S) ==> PROP S" unfolding FactCollection_imp .

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

lemma SpecTop_cong_major:
  "(P \<equiv> P') \<Longrightarrow> (PROP Q \<equiv> PROP Q') \<Longrightarrow>
  (P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP L) (PROP S)) \<equiv> (P' \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP L) (PROP S))"
    unfolding SpecTop_def by auto
(*lemma Specification_rule_aux: "(P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: Q) \<Longrightarrow> (Q \<Longrightarrow> Q') \<Longrightarrow> (P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: Q')"
    unfolding SpecTop_def  by presburger *)

section \<open>Principal rules\<close>

theorem apply_proc: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp by auto

theorem  accept_proc: "\<medium_left_bracket> \<And>s. CodeBlock s a S f \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L ) \<medium_right_bracket> \<Longrightarrow>
  CodeBlock s' a S (f \<nuInstrComp> g) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: (PROP L))" for L :: "prop" and  s' :: "('c::lrep) state"
  unfolding PropBlock_def CodeBlock_def instr_comp_def CurrentConstruction_def PendingConstruction_def
proof (rule SpecTop_I)
  assume a: "(\<And>s. a \<in> S \<and> f a = s \<and> s \<noteq> SNeg \<Longrightarrow> SPEC_TOP (bind s g \<in> \<S> T) (PROP L))" and b: " a \<in> S \<and> bind (f a) g = s' \<and> s' \<noteq> SNeg"
  from b have sa: "a \<in> S \<and> f a = f a \<and> f a \<noteq> SNeg" by (cases "f a") (auto simp add: bind_def)
  note th = a[OF sa, simplified b[THEN conjunct1]]
  from th[THEN SpecTop_focus] show "s' \<in> \<S_S> T" using b by (blast intro: LooseStateTy_upgrade)
  from th[THEN SpecTop_facts] show "PROP L" .
qed

lemma codeblock_export: "PROP Pure.prop (\<And>s. CodeBlock s a T f \<Longrightarrow> PROP C) \<Longrightarrow> PROP Pure.prop (\<And>s. CodeBlock s a T (f \<nuInstrComp> g) \<Longrightarrow> PROP C)"
 including show_more1   unfolding CodeBlock_def prop_def instr_comp_def proof -
  assume A[of "f a", simplified]: "(\<And>s. a \<in> T \<and> f a = s \<and> s \<noteq> SNeg \<Longrightarrow> PROP C)"
  fix s show "a \<in> T \<and> bind (f a) g = s \<and> s \<noteq> SNeg \<Longrightarrow> PROP C" proof -
    assume [unfolded bind_def]: "a \<in> T \<and> NuPrim.bind (f a) g = s \<and> s \<noteq> SNeg"
    then have "a \<in> T \<and> f a \<noteq> SNeg" by auto
    from this[THEN A] show "PROP C" .
  qed
qed

lemma empty_facts: "PROP FactCollection (PROP NoFact) (PROP NoFact) (PROP NoFact)"
  by ((rule FactCollection_I)?; (rule NoFact)?)

theorem start_proc:
  "CodeBlock s a S nop \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S"
  for S :: " ('a::lrep) set" and a :: 'a and s :: "'a state"
  unfolding nop_def CodeBlock_def CurrentConstruction_def by auto

theorem finish_proc: "(\<And>a s. CodeBlock s a S f \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T))
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>" for S :: "('a::lrep) set" and  T :: "('b::lrep) set"
  unfolding CodeBlock_def Procedure_def
  subgoal premises rule proof
    fix a show "a \<in> S \<longrightarrow> f a \<in> \<S> T " proof
    assume a: "a \<in> S"
    moreover note rule[of a "f a", unfolded CurrentConstruction_def, simplified] 
    ultimately show "f a \<in> \<S> T" unfolding instr_comp_def bind_def end_proc_ctx_def
      using LooseStateTy_introByStrict by (cases "f a") auto
  qed qed
  done

theorem start_block:
  "((PROP X) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<Longrightarrow>
      CodeBlock s a U nop \<Longrightarrow>
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)"
  for U :: " ('a::lrep) set" and V :: "('b::lrep) set" and s :: "'a state" and a :: 'a
  unfolding nop_def CodeBlock_def CurrentConstruction_def SpecTop_imp by (rule SpecTop_I) auto

lemma conj_imp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)" by rule simp+

lemma rename_proc: "f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U \<longmapsto> \<R> \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> \<R> \<brangle>" by fast


lemma name_star_fact:
  "(PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (Trueprop Q) (PROP L) (PROP S))
    \<Longrightarrow> (PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP NoFact) (PROP Fact name Q and_fact PROP L) (PROP S))"
  unfolding SpecTop_imp FactCollection_imp by (intro SpecTop_I FactCollection_I TrueI Fact_I AndFact_I NoFact)
lemma declare_fact:
  "A \<Longrightarrow> (PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP L) (PROP S))
    \<Longrightarrow> (PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP Fact name A and_fact PROP L) (PROP S))"
  unfolding SpecTop_imp FactCollection_imp by (intro SpecTop_I FactCollection_I TrueI Fact_I AndFact_I NoFact)

lemma set_\<nu>current:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP L) (PROP S))
    \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP L) (Trueprop (Inhabited T)))"
  unfolding SpecTop_imp FactCollection_imp by (intro SpecTop_I FactCollection_I TrueI Fact_I AndFact_I NoFact) auto

lemma clean_user_facts:
  "(PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP L) (PROP S)) \<Longrightarrow>
    (PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection NoFact NoFact (PROP S))"
  unfolding SpecTop_imp FactCollection_imp by (intro SpecTop_I FactCollection_I NoFact)

  section \<open>Supplementary structures for elementary functions\<close>

definition "SchemaTag x = x"
(* translations "x" <= "CONST SchemaTag x" *)

  subsubsection \<open>Existential Nu-type\<close>

datatype ('a,'b) to_be_bind_name = To_Be_Bind_Name 'b
definition ExTyp :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a, 'b set) to_be_bind_name" (binder "\<exists>*" 10)
  where   "ExTyp T = To_Be_Bind_Name {x. (\<exists>z. x \<in> (T z))}"
  \<comment> \<open>which represents there exists some \<nu>-images (or rarely abstractors) subject to the typing.
    And then the image subjecting the typing could be fixed as a local variable by the \<nu>-obtain command. \<close>
definition BinderNameTag :: "'b \<Rightarrow> ('b,'a) to_be_bind_name \<Rightarrow> 'a"
  where "BinderNameTag name x = (case x of To_Be_Bind_Name x' \<Rightarrow> x')"
text \<open>\<^const>\<open>BinderNameTag\<close> wraps a binding to record the variable name of a \<lambda>-abstraction as an free variable
  (e.g. \<^term>\<open>BinderNameTag var (\<exists>*var. P)\<close> for \<^term>\<open>\<exists>*var. P\<close>), in order to retain variable name during the transformation.
  The name retaining is implemented by the simple procedure `BinderNameTag` defined later.\<close>

simproc_setup BinderNameTag (\<open>BinderNameTag name (binder f)\<close>) = \<open>
  fn _ => fn ctx => fn ctm => (
    case Thm.term_of ctm of ((head1 as Const (\<^const_name>\<open>BinderNameTag\<close>, _)) $ name $ (binder $ Abs (var_name,vty,body))) =>
      if Term.term_name name = var_name then NONE
      else Thm.reflexive ctm
        |> Thm.renamed_prop (Logic.mk_equals (Thm.term_of ctm,
              (head1 $ name $ (binder $ Abs (Term.term_name name, vty, body)))))
        |> SOME
    | _ => NONE
)\<close>

lemma [simp]: "x \<in> BinderNameTag name (ExTyp T) \<equiv> (\<exists>z. x \<in> T z)" unfolding ExTyp_def BinderNameTag_def by auto
lemma [simp]: "\<S_S> (BinderNameTag name (\<exists>*x. T x)) = BinderNameTag name (\<exists>*x. \<S_S> (T x))" unfolding ExTyp_def BinderNameTag_def by auto
lemma [simp]: "(BinderNameTag name (ExTyp A) \<heavy_comma> R) = BinderNameTag name (\<exists>* x. (A x \<heavy_comma> R))" unfolding ExTyp_def BinderNameTag_def by auto
lemma [simp]: "(S\<heavy_comma>BinderNameTag name (ExTyp T)) = BinderNameTag name (\<exists>* z. (S \<heavy_comma> T z))" unfolding ExTyp_def BinderNameTag_def by auto
lemma [simp]: "\<S> (BinderNameTag name (ExTyp T)) = BinderNameTag name (\<exists>* x. \<S> (T x))" unfolding ExTyp_def BinderNameTag_def by auto
lemma [simp]: "(BinderNameTag name (ExTyp T) \<flower> R) = BinderNameTag name (\<exists>* x. (T x \<flower> R))" unfolding ExTyp_def BinderNameTag_def by auto
lemma ExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (BinderNameTag name (ExTyp T))) \<equiv> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)"
  unfolding BinderNameTag_def ExTyp_def CurrentConstruction_def by (rule eq_reflection) auto

translations "\<exists>*x r. y" => "CONST BinderNameTag x (CONST ExTyp (\<lambda>x. (\<exists>*r. y)))"
  "\<exists>*x. y" => "CONST BinderNameTag x (CONST ExTyp (\<lambda>x. y))"
  "y" <= "CONST BinderNameTag x y"
  "\<exists>*x y. z" <= "\<exists>*x. \<exists>*y. z"
  "\<exists>x y. z" <= "\<exists>x. \<exists>y. z"
  "\<exists>*a. x \<tycolon> N" == "\<exists>*a. \<tort_lbrace> x \<tycolon> N \<tort_rbrace>"

(* An example to illustrate this name retaining process *)
notepad begin
  assume "x \<in> (A\<heavy_comma>(\<exists>*aaa zz. B aaa zz)\<heavy_comma>(\<exists>*qq. C qq))"
  note this[simplified]
end

definition AutoExTyp :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" (binder "\<exists>*''" 10)
  where "AutoExTyp T = {x. (\<exists>z. x \<in> (T z))}"

lemma [simp]: "x \<in> (AutoExTyp T) \<equiv> (\<exists>z. x \<in> T z)" unfolding AutoExTyp_def by auto
lemma [simp]: "(R\<heavy_comma> AutoExTyp T) = (\<exists>*' x. (R\<heavy_comma> T x))" unfolding AutoExTyp_def by auto
lemma [simp]: "(AutoExTyp T\<heavy_comma> R) = (\<exists>*' x. (T x\<heavy_comma> R))" unfolding AutoExTyp_def by auto
lemma [simp]: "(AutoExTyp T \<flower> R) = (\<exists>*' x. (T x \<flower> R))" unfolding AutoExTyp_def BinderNameTag_def by auto

lemma [simp]: "AutoExTyp T = (\<exists>*' a b. T (a,b))" unfolding AutoExTyp_def by auto

lemma AutoExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (AutoExTyp T)) \<equiv> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)"
  unfolding AutoExTyp_def CurrentConstruction_def by (rule eq_reflection) auto

  subsubsection \<open>Addition Nu-type : coheres true proposition\<close>

definition AddtionTy :: " 'a set \<Rightarrow> bool \<Rightarrow> 'a set " (infixl "\<addition>" 50) where " T \<addition> P = {x. x \<in> T \<and> P}"
lemma [simp]: "T \<addition> True = T" unfolding AddtionTy_def by fast
lemma [simp]: "\<S_S> (T \<addition> P) = (\<S_S> T \<addition> P)" unfolding AddtionTy_def by auto
lemma [simp]: "x \<in> (T \<addition> P) \<longleftrightarrow> x \<in> T \<and> P" unfolding AddtionTy_def by auto
lemma [intro]: "P \<Longrightarrow> x \<in> T \<Longrightarrow> x \<in> (T \<addition> P)" unfolding AddtionTy_def by auto
lemma [elim]: "x \<in> (T \<addition> P) \<Longrightarrow> (x \<in> T \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C" unfolding AddtionTy_def by auto
lemma [simp]: "(R \<heavy_comma> T \<addition> P) = ((R \<heavy_comma> T) \<addition> P)" and [simp]: "(A \<addition> P \<flower> B) = ((A \<flower> B) \<addition> P)"
  and [simp]: "(A \<flower> B \<addition> P) = ((A \<flower> B) \<addition> P)"
    unfolding AddtionTy_def by auto
lemma t1: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<addition> P) \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P" unfolding CurrentConstruction_def AddtionTy_def by (cases s) auto
lemma [simp]: "((((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<and> B) \<and> C) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<equiv> (((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<and> (B \<and> C)) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)" by simp


lemma move_fact_to_star1[simp]:
  "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<addition> Q) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP NoFact) (PROP L) (PROP I))
    \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (Trueprop Q) (PROP L) (PROP I))"
  unfolding t1 SpecTop_imp conj_imp FactCollection_imp
  by (intro equal_intr_rule SpecTop_I FactCollection_I conjI NoFact) (* (unfold SpecTop_imp conj_imp FactCollection_imp) *)
lemma move_fact_to_star2[simp]:
  "((\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<addition> Q) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (Trueprop P) (PROP L) (PROP I))
    \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection  (Trueprop (Q \<and> P)) (PROP L) (PROP I))"
  unfolding t1 SpecTop_imp conj_imp FactCollection_imp
  by (intro equal_intr_rule SpecTop_I FactCollection_I conjI) (* (unfold SpecTop_imp conj_imp FactCollection_imp) *)

  subsubsection \<open>Cast\<close>

definition Cast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _/ \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e _)" [2,2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P) \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B \<and> P)"
consts SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
translations "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B)" == "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e CONST True)"
translations "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P"
(* abbreviation SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<equiv> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e True)" *)
lemma Inhabited_subset: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Inhabited B" unfolding Inhabited_def by auto
lemma CastE[elim]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Cast_def Inhabited_def by (auto intro: Inhabited_subset)
lemma CastI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" unfolding Cast_def Inhabited_def by auto
lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" by blast
lemma "=_\<nu>cast": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto
lemma [\<nu>intro']: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e N = N' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<longmapsto> \<tort_lbrace>x' \<tycolon> N'\<tort_rbrace>" unfolding Cast_def Premise_def by simp
lemma [\<nu>intro0]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x" unfolding Premise_def by simp
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t \<S_S> A \<longmapsto> \<S_S> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" by blast
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P2 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<heavy_comma>B) \<longmapsto> (A'\<heavy_comma>B') \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P1 \<and> P2" by blast
lemma LooseState_Cast[\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t \<S> A \<longmapsto> \<S> B" unfolding \<nu>def Cast_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A \<flower> B) \<longmapsto> (A' \<flower> B') \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<and> Q"
  unfolding Cast_def by auto
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A and_ty B) \<longmapsto> (A' and_ty B') \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<and> Q"
  unfolding Cast_def by auto

theorem apply_cast: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> X \<flower> W)) \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> Y \<flower> W) \<addition> P)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp by (auto 4 6)
theorem apply_cast': "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> X)) \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> Y) \<addition> P)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp by (auto 4 6)
theorem cast: "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  for T' :: "('a::lrep) set" unfolding Cast_def CurrentConstruction_def by auto

theorem proc_cast': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> A \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A' \<longmapsto> B' \<brangle>"
  unfolding Procedure_def Cast_def by (auto 0 3)

subsubsection \<open>Conversion\<close>

definition AutoTag :: "bool \<Rightarrow> bool" ("\<^bold>a\<^bold>u\<^bold>t\<^bold>o _" [100] 99) where [\<nu>def]: "\<^bold>a\<^bold>u\<^bold>t\<^bold>o P \<longleftrightarrow> P"
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U \<longmapsto> U' \<Longrightarrow> \<^bold>a\<^bold>u\<^bold>t\<^bold>o \<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> U \<longmapsto> U' \<brangle>"
  unfolding AutoTag_def Cast_def Procedure_def nop_def by auto
  
definition Conversion :: "( ('a::lrep) \<Rightarrow> ('b::lrep) state) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ( ('c::lrep) \<Rightarrow> ('d::lrep) state) \<Rightarrow> 'c set \<Rightarrow> 'd set \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)/ \<long_dobule_mapsto> _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)" [101,2,2,101,2,2] 100)
  where [\<nu>def]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> g \<blangle> U' \<longmapsto> V' \<brangle> \<longleftrightarrow>( \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> V' \<brangle> )"
lemma conversion: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f' \<blangle> U' \<longmapsto> V' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U' \<longmapsto> V' \<brangle>"
  for f :: " ('a::lrep) \<Rightarrow> ('b::lrep) state" and f' :: " ('c::lrep) \<Rightarrow> ('d::lrep) state" unfolding Conversion_def by fast
lemma [\<nu>intro]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U \<longmapsto> V \<brangle>" unfolding Conversion_def by fast
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t V \<longmapsto> V' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U' \<longmapsto> V'\<brangle>"
  unfolding Conversion_def Procedure_def Cast_def  by (auto 4 3 dest: LooseState_Cast[unfolded Cast_def, simplified])
lemma [\<nu>intro]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> g \<blangle> U' \<longmapsto> V' \<brangle> \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> call g \<blangle> U' \<flower> W \<longmapsto> V' \<flower> W\<brangle>"
  unfolding Conversion_def using call by fast
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> U \<brangle> \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> (g \<nuInstrComp> f) \<blangle> U' \<longmapsto> V\<brangle>"
  unfolding AutoTag_def Conversion_def using instr_comp by fast

theorem apply_proc_conv: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> S' \<longmapsto> T' \<brangle> \<long_dobule_mapsto> g \<blangle> S \<longmapsto> T\<brangle>) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S' \<longmapsto> T' \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Conversion_def by auto

subsubsection \<open>Auto construct & destruct\<close>

definition AutoConstruct :: " 'exp \<Rightarrow> (('a::lrep) \<Rightarrow> ('b::lrep) state) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool " ("\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t _/ \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<blangle>_/ \<longmapsto> _ \<brangle>)" [20,101,10,10] 100)
  where [\<nu>def]:"AutoConstruct exp f S T \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>"
lemma AutoConstruct: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> AutoConstruct exp f S T \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)" for exp :: "'exp"
  unfolding AutoConstruct_def using apply_proc .

lemma [\<nu>intro]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t X \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle>A \<longmapsto> B\<brangle> \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t X \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c call f \<blangle>(A \<flower> U) \<longmapsto> (B \<flower> U) \<brangle>"
  unfolding AutoConstruct_def using call by fast

lemma [simp]: "(Inhabited A \<and> Inhabited B) \<or> (Inhabited A' \<and> Inhabited B')
  \<Longrightarrow> (A\<heavy_comma>B) = (A'\<heavy_comma>B') \<longleftrightarrow> A = A' \<and> B = B'" unfolding Stack_Delimiter_def Inhabited_def by (auto simp add: times_eq_iff) 
lemma  [elim]: "(A\<heavy_comma>B) = (A'\<heavy_comma>B') \<Longrightarrow> (A = {} \<or> B = {} \<Longrightarrow> A' = {} \<or> B' = {} \<Longrightarrow> C) \<Longrightarrow> (A = A' \<Longrightarrow> B = B' \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Stack_Delimiter_def by (auto simp add: times_eq_iff)

  section \<open>Appendix\<close>

subsection \<open>Finalize the syntax sugars to be ready for use\<close>

no_translations "_pretty_and_ P Q" <= "CONST AndFact P Q"
translations "_linebreak_collection_ P Q" <= "CONST AndFact P Q"
translations "P" <= "CONST AndFact P (CONST NoFact)"

end
