(* KEEP IT SIMPLE AND STUPID *)

theory NuPrime \<comment> \<open>The Primary Theory of the \<nu>-System\<close>
  imports Main "HOL-Library.Monad_Syntax" NuHelpMath
  abbrevs "<is>" = "\<^bold>i\<^bold>s"
      and "as" = "\<^bold>a\<^bold>s"
      and "<at>" = "\<^bold>a\<^bold>t"
      and "<and>" = "\<^bold>a\<^bold>n\<^bold>d"
      and "in" = "\<^bold>i\<^bold>n"
      and "<with>" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
      and "auxiliary_facts" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "auxfacts" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "<proc>" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
      and "<map>" = "\<^bold>m\<^bold>a\<^bold>p"
      and "<param>" = "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m"
      and ",," = "\<heavy_comma>"
      and "<cast>" = "\<^bold>c\<^bold>a\<^bold>s\<^bold>t"
      and "<claim>" = "\<^bold>c\<^bold>l\<^bold>a\<^bold>i\<^bold>m"
      and "<conversion>" = "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n"
      and "<auto>" = "\<^bold>a\<^bold>u\<^bold>t\<^bold>o"
      and "<premise>" = "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e"
      and atomic = "\<^bold>a\<^bold>t\<^bold>o\<^bold>m\<^bold>i\<^bold>c"
      and construct = "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t"
      and "by" = "\<^bold>b\<^bold>y"
      and "<simplify>" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y"
      and "<END>" = "\<^bold>E\<^bold>N\<^bold>D"
      and "<heap>" = "\<^bold>h\<^bold>e\<^bold>a\<^bold>p"
      and "<stack>" = "\<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k"
      and "<dual>" = "\<^bold>d\<^bold>u\<^bold>a\<^bold>l"
      and "<when>" = "\<^bold>w\<^bold>h\<^bold>e\<^bold>n"
      and "<intro>" = "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o"
      and "<dest>" = "\<^bold>d\<^bold>e\<^bold>s\<^bold>t"
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
  (* and \<nu>address_def \<open>primitive definitions for unfolding in proofs for address\<close> *)
  and \<nu>post_construct and \<nu>auto_destruct
named_theorems typing_expn "expansion theorems for abstractions" and lrep_exps

declare conjI[\<nu>intro] TrueI[\<nu>intro]

subsection \<open>Syntax and Notations\<close>

(* consts "ARBITRARY___" :: 'a ("\<cdots>") \<comment>\<open>merely a sugar for documenting\<close> *)

definition PropBlock :: "prop \<Rightarrow> prop" ("\<medium_left_bracket> _ \<medium_right_bracket>" [0] 1000) where "PropBlock p \<equiv> p"
  \<comment>\<open>The block of proposition has specific meaning in \<nu>-system.
  @{prop "A \<Longrightarrow> B \<Longrightarrow> C"} represents an forward construction rule to finally construct @{term C}.
  The construction rule could be high-order parametric, e.g. @{prop "A \<Longrightarrow> \<medium_left_bracket> B \<Longrightarrow> C \<Longrightarrow> D \<medium_right_bracket> \<Longrightarrow> E"},
    and in those cases the high-order parameter is wrapped by @{term Pure.prop} to become an atomic
    premise in order to disambiguate with the semantics of nested hypothesises.\<close>
lemmas  PropBlock_I = PropBlock_def[THEN equal_elim_rule2]
lemmas  PropBlock_D = PropBlock_def[THEN equal_elim_rule1]

syntax
  "_linebreak_" :: "logic \<Rightarrow> logic" ("//\<zero_width_space>_" [3] 3)
  "_linebreak_collection_" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  ("_//\<invisible_separator>_" [4,3] 3)
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

definition ProtectorI :: "'a \<Rightarrow> 'a" where "ProtectorI x = x"
lemma [cong]: "ProtectorI X \<equiv> ProtectorI X" .

definition WorkingProtector :: "'a \<Rightarrow> 'a" where "WorkingProtector x \<equiv> x"

subsubsection \<open>Structures assembling propositions\<close>

definition NoFact :: "prop" ("\<^bold>n\<^bold>o\<^bold>t\<^bold>h\<^bold>i\<^bold>n\<^bold>g") where "NoFact \<equiv> Trueprop True"
lemma NoFact: "PROP NoFact" unfolding NoFact_def using TrueI .
definition AndFact :: "prop \<Rightarrow> prop \<Rightarrow> prop" (infixr "and'_fact" 3) where "AndFact \<equiv> (&&&)"

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

(* datatype zint = Gz | Gi int
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
*)
section\<open>Low representation for semantics\<close>

datatype msegment = Null (*address space*) nat | MSegment nat
type_synonym addr_space = nat
  \<comment> \<open>Address space is a notion of the LLVM. The space 0 is the main memory of the device.
    Space other than 0 is specified depending on platform, which may represent addresses on remote devices like display card\<close>

datatype 'offset memaddr = memaddr (segment_of: msegment) (offset_of: 'offset ) (infixl "|+" 60)
declare memaddr.sel[iff]

abbreviation shift_addr :: " 'a::plus memaddr \<Rightarrow> 'a \<Rightarrow> 'a memaddr" (infixl "||+" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. x + delta) addr"
lemma memaddr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>base ofs. P (base  |+ ofs))" by (metis memaddr.exhaust)
lemma memaddr_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>base ofs. P (base  |+ ofs))" by (metis memaddr.exhaust)

datatype deep_model = DM_int nat nat | DM_pointer "nat memaddr" | DM_fusion deep_model deep_model
  | DM_record deep_model | DM_array "deep_model list" | DM_none

datatype resource_key = MemAddress "nat memaddr" | ChainDB_key nat
  \<comment> \<open>The write operation on address `addr` requires owning of resource `MemAddress addr`,
    while the dispose of that memory on `addr` requires both owning of resource `MemAddress addr`
      and `Dispose (MemAddress addr)`\<close>

lemma resource_key_forall: "All P \<longleftrightarrow> (\<forall>addr. P (MemAddress addr)) \<and> (\<forall>n. P (ChainDB_key n))" by (metis resource_key.exhaust)
lemma resource_key_exists: "Ex P \<longleftrightarrow> (\<exists>addr. P (MemAddress addr)) \<or> (\<exists>n. P (ChainDB_key n))" by (metis resource_key.exhaust)

type_synonym heap = "resource_key \<rightharpoonup> deep_model"


definition AvailableSegments :: "heap \<Rightarrow> msegment set"
  where "AvailableSegments heap = {seg. \<forall>ofs. heap (MemAddress (seg |+ ofs)) = None}"

definition Heap :: "heap \<Rightarrow> bool" where "Heap h \<longleftrightarrow> infinite (AvailableSegments h)"

lemma [intro]: "Heap h \<Longrightarrow> Heap (h(k := v))" proof -
  have "AvailableSegments h \<subseteq> {(case k of MemAddress (seg |+ ofs) \<Rightarrow> seg)} \<union> (AvailableSegments (h(k := v)))"
    unfolding AvailableSegments_def by auto 
  then show "Heap h \<Longrightarrow> Heap (h(k := v))" 
    unfolding Heap_def using infinite_super by auto
qed


text \<open>The semantic framework follows a style of shallow embedding, where semantics for different type (e.g. integers, floats)
  are modelled by different Isabelle type. Model types are constrained by the base type class {\it lrep} and types representing
  objects that supports certain features are constrained by specific sub-classes which extend the base class {\it lrep} finally. \<close>

datatype llty = llty_int nat \<comment> \<open>int bits\<close> | llty_pointer | llty_tup llty | llty_array llty nat | llty_nil | llty_fusion llty llty

class lrep =  \<comment>\<open>The basic class for types modelling concrete objects\<close>
  fixes llty :: " 'a itself \<Rightarrow> llty "
  fixes deepize :: " 'a \<Rightarrow> deep_model "
  fixes shallowize :: " deep_model \<Rightarrow> 'a "
  assumes deepize_inj[simp]: " shallowize (deepize x) = x "

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

type_synonym ('a,'b) \<nu> = " 'a \<Rightarrow> 'b \<Rightarrow> bool "

subsection \<open>The \<nu>-type\<close>

subsubsection \<open>Definitions\<close>

(* ceq : INF *)

datatype ('a,'b) typing = typing 'b "('a,'b) \<nu>" ("_ \<tycolon> _" [16,16] 15) \<comment>\<open>shortcut keys "<ty>"\<close>
primrec nu_of :: "('a,'b) typing \<Rightarrow> ('a,'b) \<nu>" where "nu_of (x \<tycolon> N) = N"
primrec image_of :: "('a,'b) typing \<Rightarrow> 'b" where "image_of (x \<tycolon> N) = x"

definition RepSet :: "('a,'b) typing \<Rightarrow> 'a set" ("\<tort_lbrace> _ \<tort_rbrace>" [10] ) where "\<tort_lbrace> ty \<tort_rbrace> = {p. case ty of (x \<tycolon> N) \<Rightarrow> N p x }"
abbreviation Refining :: "'a \<Rightarrow> ('a,'b) \<nu> \<Rightarrow>  'b \<Rightarrow> bool" ("(_/ \<nuLinkL> _  \<nuLinkR>/ _)" [27,15,27] 26) \<comment>\<open>shortcut keys "--<" and ">--"\<close>
  where  "(p \<nuLinkL> N \<nuLinkR> x) \<equiv> p \<in> \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
definition Inhabited :: " 'a set \<Rightarrow> bool" where "Inhabited s \<equiv> (\<exists>x. x \<in> s)"
abbreviation InhabitTyp :: " 'b \<Rightarrow> ('a,'b) \<nu> \<Rightarrow> bool" ("_ \<ratio> _" [16,16] 15)  \<comment>\<open>shortcut keys ":TY:"\<close>
  where  " x \<ratio> N \<equiv> Inhabited \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
text \<open>The @{term "x \<tycolon> N"} is a predication specifying concrete values,
  e.g. @{prop " a_concrete_int32 \<in> \<tort_lbrace>(42::nat) \<tycolon> N 32\<tort_rbrace>"} and also "state \<in> State (\<tort_lbrace>42 \<tycolon> N\<tort_rbrace> \<times> \<tort_lbrace>24 \<tycolon> N\<tort_rbrace> \<times> \<cdots> )".
  It constitutes basic elements in specification.
  The @{prop "p \<nuLinkL> N \<nuLinkR> x"} as the abbreviation of $p \<in> (x \<tycolon> N)$ is an abstraction between concrete value @{term p} and
  abstracted {\it image} @{term x} via the \<nu>-{\it abstractor} @{term N} which defines the abstraction relationship itself.
  The next @{prop " x \<ratio> N"} is a proposition stating @{term x} is an image of abstractor @{term N} and therefore
  the \<nu>-type @{term "x \<tycolon> N"} is inhabited. Basically it is used to derive implicated conditions of images,
  e.g. @{prop "( 42 \<ratio> N 32) \<Longrightarrow> 42 < 2^32"}\<close>

lemma Refining_ex: " p \<nuLinkL> R \<nuLinkR> x \<longleftrightarrow> R p x" unfolding RepSet_def by auto

(* lemma [elim!,\<nu>elim]: "Inhabited (U \<times> V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> PROP C) \<Longrightarrow> PROP C" unfolding Inhabited_def by auto *)
lemma [intro]: "x \<in> S \<Longrightarrow> Inhabited S" unfolding Inhabited_def by auto
lemma Inhabited_E: "Inhabited S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto


subsubsection \<open>Properties\<close>

definition \<nu>Zero :: "('a::{zero,lrep},'b) \<nu> \<Rightarrow> 'b \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Zero N x \<longleftrightarrow> (0 \<nuLinkL> N \<nuLinkR> x )"
definition \<nu>Equal :: "('a::{lrep,ceq}, 'b) \<nu> \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Equal N can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 heap.
    can_eq x1 x2 \<and> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> N \<nuLinkR> x2) \<longrightarrow> ceqable heap p1 p2 \<and> (ceq p1 p2 = eq x1 x2))"


  section\<open>Structures for construction\<close>

subsection \<open>Auxiliary tags\<close>

subsubsection \<open>Name tag\<close>

datatype name_tag = NAME_TAG "unit \<Rightarrow> unit"
definition Named :: "name_tag \<Rightarrow> 'a \<Rightarrow> 'a" where "Named name x = x" \<comment>\<open>name tag\<close>

lemma [cong]: "NAME_TAG x \<equiv> NAME_TAG x"  using reflexive .
lemma name_tag_eq: "x = y" for x :: name_tag by (cases x, cases y) auto

syntax "_NAME_" :: "idt \<Rightarrow> name_tag" ("NAME _" [0] 1000)
  "_NAME2_" :: "idt => idt => name_tag" ("NAME2 _ _" [0,0] 1000)
translations "NAME name" == "CONST NAME_TAG (\<lambda>name. ())"

consts "named_sugar" :: " 'i_am \<Rightarrow> 'merely \<Rightarrow> 'a_sugar " ("\<ltbrak>_\<rtbrak>. _" [10,15] 14)
translations
  "\<ltbrak>name\<rtbrak>. x \<tycolon> T" == "\<ltbrak>name\<rtbrak>. \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"
  "\<ltbrak>name\<rtbrak>. x" == "CONST Named (NAME name) x"

lemma [simp]: "x \<in> Named name S \<longleftrightarrow> x \<in> S" unfolding Named_def ..
lemma [simp]: "x \<in> Named name S \<longleftrightarrow> x \<in> S" unfolding Named_def ..

subsubsection \<open>Parameter tag\<close>

definition ParamTag :: " 'a \<Rightarrow> bool" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 26) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> True"
lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
  \<comment>\<open>A tag used to indicate a parameter should be specified during application. It retains the order of the parameters to be specified.
  For example, "@{prop "\<And>bit_width value. \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_width \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> P bit_wdith value"},
    the first parameter `?bit_width` will be specified first and then the "?value".\<close>
lemma [elim!,\<nu>elim]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" by auto

subsubsection \<open>Premise tag\<close>

definition Premise :: "bool \<Rightarrow> bool" ("\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e _" [27] 26) where [\<nu>def]:"Premise x = x"
  \<comment> \<open>A tag to hint automatic provers to try to prove this proof obligation\<close>
lemma Premise_I: "P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P" unfolding Premise_def by simp
lemma Premise_E: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> P" unfolding Premise_def by simp
lemma [elim!,\<nu>elim]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> C" unfolding Premise_def by simp
lemma Premise_Irew: "(P \<Longrightarrow> C) \<equiv> Trueprop (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<longrightarrow> C)" unfolding Premise_def atomize_imp .

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

subsubsection \<open>Intro and Dest tag\<close>

definition Intro :: " bool \<Rightarrow> bool " ("\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o _") where "Intro P = P"
definition Dest :: " bool \<Rightarrow> bool " ("\<^bold>d\<^bold>e\<^bold>s\<^bold>t _") where "Dest P = P"

subsection \<open>Register and its collection\<close>

instantiation prod :: (lrep,lrep) lrep begin
definition llty_prod :: "('a \<times> 'b) itself \<Rightarrow> llty" where "llty_prod _ = llty_fusion LLTY('a) LLTY('b)"
definition deepize_prod :: " 'a \<times> 'b \<Rightarrow> deep_model " where "deepize_prod = (\<lambda>(a,b). DM_fusion (deepize a) (deepize b))"
definition shallowize_prod :: "deep_model \<Rightarrow> 'a \<times> 'b" where
  "shallowize_prod x = (case x of DM_fusion a b \<Rightarrow> (shallowize a, shallowize b))"
instance apply standard
  subgoal for x by (cases x) (auto simp add: shallowize_prod_def deepize_prod_def) done
end


subsection \<open>Stack structure\<close>

class stack = lrep

instantiation prod :: (lrep,stack) stack begin instance by standard end

subsubsection \<open>Separation Conjecture\<close>

definition disjoint :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " (infixl "\<perpendicular>" 60) where "disjoint A B \<longleftrightarrow> (A \<inter> B = {})"
lemma disjoint_rewL: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<notin> B)" unfolding disjoint_def by auto
lemma disjoint_rewR: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> B \<longrightarrow> x \<notin> A)" unfolding disjoint_def by auto

lemma [iff]: "{} \<perpendicular> S" and [iff]: "S \<perpendicular> {}" unfolding disjoint_def by auto

definition Separation :: " heap set \<Rightarrow> heap set \<Rightarrow> heap set" (infixl "\<heavy_asterisk>" 14)
  where "Separation H1 H2 = {h. (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> h1 \<in> H1 \<and> h2 \<in> H2) }"
definition NonSeparation :: " heap set \<Rightarrow> heap set \<Rightarrow> heap set" (infixl "\<dbl_and>" 13)
  where "NonSeparation H1 H2 = {h. h \<in> H1 \<and> (\<exists>h'. h' \<subseteq>\<^sub>m h \<and> h' \<in> H2)}"

translations
  "H \<heavy_asterisk> x \<tycolon> T" == "H \<heavy_asterisk> \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"
  "x \<tycolon> T \<heavy_asterisk> H" == "\<tort_lbrace> x \<tycolon> T \<tort_rbrace> \<heavy_asterisk> H"
  "H \<dbl_and> x \<tycolon> T" == "H \<dbl_and> \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"
  "x \<tycolon> T \<dbl_and> H" == "\<tort_lbrace> x \<tycolon> T \<tort_rbrace> \<dbl_and> H"

lemma [iff]: "h \<in> (H1 \<heavy_asterisk> H2) \<longleftrightarrow> (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> h1 \<in> H1 \<and> h2 \<in> H2)" unfolding Separation_def by simp
lemma [iff]: "h \<in> (H1 \<dbl_and> H2) \<longleftrightarrow> (h \<in> H1 \<and> (\<exists>h'. h' \<subseteq>\<^sub>m h \<and> h' \<in> H2))" unfolding NonSeparation_def by simp

lemma [simp]: "A \<inter> S \<perpendicular> A \<inter> -S"
  unfolding disjoint_def by auto
lemma heap_split_id: "P h1' h2' \<Longrightarrow> \<exists>h1 h2. h1' ++ h2' = h1 ++ h2 \<and> P h1 h2" by auto
lemma heap_split_by_set: "P (h |` S) (h |` (- S)) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  by (rule exI[of _ "h |` S"], rule exI[of _ "h |` (- S)"])
    (auto simp add: map_add_def option.case_eq_if restrict_map_def disjoint_def disjoint_iff domIff)
lemma heap_split_by_addr_set: "P (h |` (MemAddress ` S)) (h |` (- (MemAddress ` S))) \<Longrightarrow> \<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> P h1 h2"
  using heap_split_by_set .

lemma Separation_comm: "(P \<heavy_asterisk> Q) = (Q \<heavy_asterisk> P)"
  by(auto simp add:Separation_def disjoint_def dest: map_add_comm)
lemma Separation_assoc: "(A \<heavy_asterisk> (B \<heavy_asterisk> C)) = (A \<heavy_asterisk> B \<heavy_asterisk> C)"
  by (auto simp add:Separation_def disjoint_def) 
    (metis (no_types, lifting) Un_empty dom_map_add inf_sup_distrib1 inf_sup_distrib2 map_add_assoc)+

lemma NonSeparation_distrib_L: "h \<in> (A \<heavy_asterisk> (B \<dbl_and> P)) \<Longrightarrow> h \<in> (A \<heavy_asterisk> B \<dbl_and> P)"
  using map_le_map_add map_le_trans by blast
lemma NonSeparation_distrib_R: "h \<in> ((A \<dbl_and> P) \<heavy_asterisk> B) \<Longrightarrow> h \<in> (A \<heavy_asterisk> B \<dbl_and> P)"
  by (metis NonSeparation_distrib_L Separation_comm)
  

lemma [elim!,\<nu>elim]: "Inhabited (A \<heavy_asterisk> B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by auto
lemma [elim!,\<nu>elim]: "Inhabited (A \<dbl_and> B) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by auto

subsubsection \<open>Delimiter operator\<close>

definition Stack_Delimiter :: " ('a :: stack) set \<Rightarrow> ('b :: lrep) set \<Rightarrow> ('b \<times> 'a) set " ( "_/ \<heavy_comma> _" [14,15] 14)
  where "Stack_Delimiter A B = (B \<times> A)"
translations "R \<heavy_comma> x \<tycolon> N" == "R \<heavy_comma> \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
  "x \<tycolon> N \<heavy_comma> R" == "\<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<heavy_comma> R"

lemma [simp]: " (a,b) \<in> (B \<heavy_comma> A) \<longleftrightarrow> a \<in> A \<and> b \<in> B" unfolding Stack_Delimiter_def by simp
(* lemma [intro]: "[heap] a \<in>\<^sub>\<nu> A \<Longrightarrow> [heap] b \<in>\<^sub>\<nu> B \<Longrightarrow> [heap] (a,b) \<in>\<^sub>\<nu> (B \<heavy_comma> A)" by simp
lemma [elim]: "[heap] ab \<in>\<^sub>\<nu> (B \<heavy_comma> A) \<Longrightarrow> (\<And>a b. ab = (a,b) \<Longrightarrow> [heap] a \<in>\<^sub>\<nu> A \<Longrightarrow> [heap] b \<in>\<^sub>\<nu> B \<Longrightarrow> C) \<Longrightarrow> C" by (cases ab) simp *)
lemma [elim!,\<nu>elim]: "Inhabited (U\<heavy_comma>V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

subsubsection \<open>Context Type\<close>

definition Context :: " ('a :: stack) set \<Rightarrow> heap set \<Rightarrow> (heap \<times> 'a) set " ( "(2_ \<heavy_comma>/ \<^bold>h\<^bold>e\<^bold>a\<^bold>p _)" [10,14] 13)
  where "(S \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) = {(h,s). h \<in> H \<and> Heap h \<and> s \<in> S}"

lemma [simp]: " (h,s) \<in> (S \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<longleftrightarrow> h \<in> H \<and> Heap h \<and> s \<in> S" unfolding Context_def by simp
lemma [elim!,\<nu>elim]: "Inhabited (S \<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<Longrightarrow> (Inhabited S \<Longrightarrow> Inhabited H \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

subsubsection \<open>Tag: End_of_Contextual_Stack\<close>

definition End_of_Contextual_Stack :: " 'a \<Rightarrow> 'a " ("\<^bold>E\<^bold>N\<^bold>D") where [\<nu>def]: "End_of_Contextual_Stack x = x" \<comment> \<open>A tag for printing sugar\<close>
lemmas End_of_Contextual_Stack_rew = End_of_Contextual_Stack_def[THEN eq_reflection]
lemma [elim,\<nu>elim]: "Inhabited (End_of_Contextual_Stack S) \<Longrightarrow> C \<Longrightarrow> C" .

subsection \<open>The \<nu>-system VM and Procedure construction structures\<close>

datatype 'a state = Success "heap \<times> 'a" | Fail | PartialCorrect
text\<open> The basic state of the \<nu>-system virtual machine is represented by type @{typ "('a::lrep) state"}.
  The valid state `Success` essentially has two major form, one without registers and another one with them,
      \<^item> "StatOn (x1, x2, \<cdots>, xn, void)",
  where "(x1, x2, \<cdots>, xn, void)" represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term PartialCorrect} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term PartialCorrect} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>

declare state.split[split]

subsubsection \<open>Types specifying states\<close>

definition StrictStateTy :: " (heap \<times> 'a::lrep) set \<Rightarrow> 'a state set" ("\<S_S> _" [56] 55)
  where "\<S_S> T = {s. case s of Success x \<Rightarrow> x \<in> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"
definition LooseStateTy :: " (heap \<times> 'a::lrep) set \<Rightarrow> 'a state set" ("\<S> _" [56] 55)
  where "\<S> T = {s. case s of Success x \<Rightarrow> x \<in> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma [simp]: "Success x \<in> \<S_S> T \<equiv> x \<in> T" and [simp]: "\<not> (Fail \<in> \<S_S> T)" and [simp]: "\<not> (PartialCorrect \<in> \<S_S> T)"
  and [simp]: "Success x \<in> \<S> T \<equiv> x \<in> T" and [simp]: "\<not> (Fail \<in> \<S> T)" and [simp]: "(PartialCorrect \<in> \<S> T)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
(* lemma [dest]: "s \<in> \<S_S> T \<Longrightarrow> Inhabited T" unfolding Inhabited_def by (cases s) auto *)
    \<comment>\<open>The inhabited property can be inferred from @{term StrictStateTy} only rather than @{term LooseStateTy}. \<close>
lemma [elim]: "s \<in> \<S_S> T \<Longrightarrow> (\<And>x. s = Success x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma [intro]: " x \<in> T \<Longrightarrow> Success x \<in> \<S_S> T" by simp
lemma [elim]: "s \<in> \<S> T \<Longrightarrow> (\<And>x. s = Success x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma [intro]: " x \<in> T \<Longrightarrow> Success x \<in> \<S> T" and [intro]: "PartialCorrect \<in> \<S> T" by simp_all
lemma LooseStateTy_upgrade: "s \<in> \<S> T \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> \<S_S> T" by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> \<S_S> T \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> \<S_S> T) \<Longrightarrow> s \<in> \<S> T" by (cases s) auto

subsubsection \<open>\<nu>-Procedure\<close>

type_synonym ('a,'b) proc = " (heap \<times> 'a) \<Rightarrow> 'b state" (infix "\<longmapsto>" 0)
definition Procedure :: "('a \<longmapsto> 'b) \<Rightarrow> (heap \<times> 'a::lrep) set \<Rightarrow> (heap \<times> 'b::lrep) set \<Rightarrow> bool" ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ \<blangle>(2 _/  \<longmapsto>  _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]:"Procedure f T U \<longleftrightarrow> (\<forall>a. a \<in> T \<longrightarrow> f a \<in> \<S> U)"

definition Map :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set " where "Map A B = {f. \<forall>a. a \<in> A \<longrightarrow> f a \<in> B }"
definition Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<blangle>(2 _/ \<longmapsto> _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle> \<equiv> \<forall>a. a \<in> T \<longrightarrow> f a \<in> U"
(* lemma [intro]: "(\<And>x h. x \<in> T h \<Longrightarrow> f x \<in> U h) \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle>" by auto *)
(* lemma [simp]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> \<S> U \<brangle> \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> T \<longmapsto> U \<brangle>" unfolding \<nu>def by fast  *)

subsection \<open>Primitive operations and instructions required in the system\<close>

subsubsection \<open>Elementary instructions\<close>

definition bind :: " ('a::lrep) state \<Rightarrow> ( 'a \<longmapsto> 'b) \<Rightarrow> ('b::lrep) state " \<comment>\<open>monadic bind\<close>
  where "bind s f = (case s of Success x \<Rightarrow> f x | Fail \<Rightarrow> Fail | PartialCorrect \<Rightarrow> PartialCorrect)"
definition instr_comp :: "(('a::lrep) \<longmapsto> ('b::lrep)) \<Rightarrow> ( 'b \<longmapsto> ('c::lrep)) \<Rightarrow> 'a \<longmapsto> 'c"  ("_ \<nuInstrComp>/ _" [75,76] 75) 
  where "instr_comp f g s = bind (f s) g"
definition nop :: " ('a::lrep) \<longmapsto> 'a" where "nop = Success" \<comment>\<open>the instruction `no-operation`\<close>

lemma nop_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> T \<longmapsto> T \<brangle>" unfolding nop_def Procedure_def by auto
lemma instr_comp[intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> B \<longmapsto> C \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> g) \<blangle> A \<longmapsto> C \<brangle>"
  unfolding instr_comp_def Procedure_def bind_def by auto fastforce+


subsection \<open>Top-level Construction Structures\<close>

subsubsection \<open>Construction Context & Code block\<close>

definition CurrentConstruction :: " ('a::lrep) state \<Rightarrow> (heap \<times> 'a) set \<Rightarrow> bool " ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,11] 10)
  where "CurrentConstruction s S \<longleftrightarrow> s \<in> \<S_S> S"
definition PendingConstruction :: " (('a::lrep) \<longmapsto> ('b::lrep)) \<Rightarrow> 'a state \<Rightarrow> (heap \<times> 'b) set \<Rightarrow> bool " ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,5] 4)
  where "PendingConstruction f s S \<longleftrightarrow> bind s f \<in> \<S> S"

lemma [elim!,\<nu>elim]: "CurrentConstruction s S \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding CurrentConstruction_def by (cases s) auto

definition CodeBlock :: " ('a::lrep) state \<Rightarrow> heap \<times> ('b::lrep) => (heap \<times> 'b) set \<Rightarrow> ('b \<longmapsto> 'a) \<Rightarrow> bool" where
  CodeBlock_def: "CodeBlock stat arg ty prog \<longleftrightarrow> (arg \<in> ty \<and> prog arg = stat \<and> stat \<noteq> PartialCorrect)"
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

lemma [elim!,\<nu>elim]: "CodeBlock v arg ty prog \<Longrightarrow> (Inhabited ty \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding CodeBlock_def by auto
lemma CodeBlock_unabbrev: "CodeBlock v arg ty prog \<Longrightarrow> (v \<equiv> ProtectorI (prog arg))"
  unfolding CodeBlock_def ProtectorI_def by (rule eq_reflection) fast
lemma CodeBlock_abbrev: "CodeBlock v arg ty prog \<Longrightarrow> ProtectorI (prog arg) \<equiv> v"
  unfolding CodeBlock_def ProtectorI_def by (rule eq_reflection) fast

subsubsection \<open>Contextual Fact\<close>

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

lemma empty_facts: "PROP FactCollection (PROP NoFact) (PROP NoFact) (PROP NoFact)"
  by ((rule FactCollection_I)?; (rule NoFact)?)

subsubsection \<open>Top structure of the sequent\<close>

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
  subgoal premises prems proof (rule SpecTop_I)
  from prems(2) have sa: "a \<in> S \<and> f a = f a \<and> f a \<noteq> PartialCorrect" 
    by (cases "f a") (auto simp add: bind_def)
  note th = prems(1)[OF sa, simplified prems(2)[THEN conjunct1]]
  from th[THEN SpecTop_focus] show "s' \<in> \<S_S> T" using prems(2) by (blast intro: LooseStateTy_upgrade)
  from th[THEN SpecTop_facts] show "PROP L" .
qed done

lemma codeblock_export: "PROP Pure.prop (\<And>s. CodeBlock s a T f \<Longrightarrow> PROP C) \<Longrightarrow> PROP Pure.prop (\<And>s. CodeBlock s a T (f \<nuInstrComp> g) \<Longrightarrow> PROP C)"
  unfolding CodeBlock_def prop_def instr_comp_def proof -
  assume A[of "f a", simplified]: "(\<And>s. a \<in> T \<and> f a = s \<and> s \<noteq> PartialCorrect \<Longrightarrow> PROP C)"
  fix s show "a \<in> T \<and> bind (f a) g = s \<and> s \<noteq> PartialCorrect \<Longrightarrow> PROP C" proof -
    assume [unfolded bind_def]: "a \<in> T \<and> bind (f a) g = s \<and> s \<noteq> PartialCorrect"
    then have "a \<in> T \<and> f a \<noteq> PartialCorrect" by auto
    from this[THEN A] show "PROP C" .
  qed
qed

theorem start_proc:
  "CodeBlock s a S nop \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S"
  for S :: " (heap \<times> 'a::lrep) set" and a :: "heap \<times> 'a" and s :: "'a state"
  unfolding nop_def CodeBlock_def CurrentConstruction_def by auto

theorem finish_proc: "(\<And>a s. CodeBlock s a S f \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T))
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>" for S :: "(heap \<times> 'a::lrep) set" and  T :: "(heap \<times> 'b::lrep) set"
  unfolding CodeBlock_def Procedure_def
  subgoal premises rule apply (rule,rule) subgoal premises a for a proof -
    note rule[of "a" "f a", unfolded CurrentConstruction_def, simplified] 
    then show "f a \<in> \<S> T" unfolding instr_comp_def bind_def
      using LooseStateTy_introByStrict a by (cases "f a") auto
  qed done done

theorem start_block:
  "((PROP X) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<Longrightarrow>
      CodeBlock s a U nop \<Longrightarrow>
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)"
  for U :: " (heap \<times> 'a::lrep) set" and V :: "(heap \<times> 'b::lrep) set" and s :: " 'a state" and a :: "heap \<times> 'a"
  unfolding nop_def CodeBlock_def CurrentConstruction_def SpecTop_imp by (rule SpecTop_I) auto

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

  section \<open>Supplementary structures and mechanisms for elementary functions\<close>

definition "SchemaTag x = x"
(* translations "x" <= "CONST SchemaTag x" *)

  subsubsection \<open>Existential Nu-type\<close>

definition ExTyp :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" (binder "\<exists>* " 10)
  where   "ExTyp T = {x. (\<exists>z. x \<in> T z)}"
notation ExTyp (binder "\<exists>'' " 10)
  \<comment> \<open>which represents there exists some \<nu>-images (or rarely abstractors) subject to the typing.
    And then the image subjecting the typing could be fixed as a local variable by the \<nu>-obtain command. \<close>

lemma [simp]: "x \<in> ExTyp T \<longleftrightarrow> (\<exists>z. x \<in> T z)" unfolding ExTyp_def  by auto
lemma [simp]: "x \<in> \<S> (ExTyp T) \<longleftrightarrow> (\<exists>z. x \<in> \<S> (T z))" by (auto 4 3)
lemma [simp]: "x \<in> \<S_S> (ExTyp T) \<longleftrightarrow> (\<exists>z. x \<in> \<S_S> (T z))" by (auto 4 3)
lemma [simp]: "(ExTyp A \<heavy_comma> R) = (\<exists>* x. (A x \<heavy_comma> R))" by auto
lemma [simp]: "(S\<heavy_comma> ExTyp T) = (\<exists>* z. (S \<heavy_comma> T z))" by auto
lemma ExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (ExTyp T)) \<equiv> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)"
  unfolding CurrentConstruction_def by auto


(* definition AutoExTyp :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" (binder "\<exists>*''" 10)
  where "AutoExTyp T = {x. (\<exists>z. x \<in> (T z))}"

lemma [simp]: "x \<in> (AutoExTyp T) \<equiv> (\<exists>z. x \<in> T z)" unfolding AutoExTyp_def by auto
lemma [simp]: "(R\<heavy_comma> AutoExTyp T) = (\<exists>*' x. (R\<heavy_comma> T x))" unfolding AutoExTyp_def by auto
lemma [simp]: "(AutoExTyp T\<heavy_comma> R) = (\<exists>*' x. (T x\<heavy_comma> R))" unfolding AutoExTyp_def by auto
lemma [simp]: "(AutoExTyp T \<flower> R) = (\<exists>*' x. (T x \<flower> R))" unfolding AutoExTyp_def BinderNameTag_def by auto

lemma [simp]: "AutoExTyp T = (\<exists>*' a b. T (a,b))" unfolding AutoExTyp_def by auto

lemma AutoExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (AutoExTyp T)) \<equiv> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)"
  unfolding AutoExTyp_def CurrentConstruction_def by (rule eq_reflection) auto *)

  subsubsection \<open>Addition Nu-type : coheres true proposition\<close>

definition AddtionTy :: " 'a set \<Rightarrow> bool \<Rightarrow> 'a set " (infixl "\<addition>" 50)
  where " (T \<addition> P) = {x. x \<in> T \<and> P}"
lemma [simp]: "T \<addition> True = T" unfolding AddtionTy_def by simp
lemma [simp]: "x \<in> (T \<addition> P) \<longleftrightarrow> x \<in> T \<and> P" unfolding AddtionTy_def by simp
(* lemma [intro]: "P \<Longrightarrow> [h] x \<in>\<^sub>\<nu> T \<Longrightarrow> [h] x \<in>\<^sub>\<nu> (T \<addition> P)" by simp
lemma [elim]: "[h] x \<in>\<^sub>\<nu> (T \<addition> P) \<Longrightarrow> ([h] x \<in>\<^sub>\<nu> T \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C" by simp*)
lemma [simp]: "(R \<heavy_comma> T \<addition> P) = ((R \<heavy_comma> T) \<addition> P)" by auto
lemma t1: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<addition> P) \<longleftrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P" unfolding CurrentConstruction_def by (cases s) auto
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

  subsection \<open>Cast\<close>

definition Cast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _)" [2,2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B \<and> P)"
consts SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _)" [2,14] 13)
translations "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B)" == "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True)"


definition CastDual :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _/ \<^bold>w\<^bold>h\<^bold>e\<^bold>n _)" [2,2,2,2,14] 13)
  where "CastDual A B P A' B' P' \<longleftrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<and> (P' \<longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> B'))"
consts SimpCastDual1 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _/ \<^bold>w\<^bold>h\<^bold>e\<^bold>n _)" [2,2,2,14] 13)
consts SimpCastDual2 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>w\<^bold>i\<^bold>t\<^bold>h _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [2,2,2,14] 13)
consts SimpCastDual3 :: " 'a set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _/ \<longmapsto> _/ \<^bold>d\<^bold>u\<^bold>a\<^bold>l _/ \<longmapsto> _)" [2,2,14] 13)
translations
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n CONST True"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h CONST True \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B'" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n CONST True"

translations "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace>a \<tycolon> A\<tort_rbrace> \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l a' \<tycolon> A' \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<tort_lbrace>a' \<tycolon> A'\<tort_rbrace> \<longmapsto> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> b' \<tycolon> B' \<^bold>w\<^bold>h\<^bold>e\<^bold>n P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P' \<^bold>d\<^bold>u\<^bold>a\<^bold>l A' \<longmapsto> \<tort_lbrace>b' \<tycolon> B'\<tort_rbrace> \<^bold>w\<^bold>h\<^bold>e\<^bold>n P"

(* abbreviation SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<equiv> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h True)" *)
(* lemma CastE[elim]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Cast_def Inhabited_def by (auto intro: Inhabited_subset)
lemma CastI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Cast_def Inhabited_def by auto *)
lemma cast_id[\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" unfolding Cast_def by fast
lemma cast_dual_id[\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A \<^bold>d\<^bold>u\<^bold>a\<^bold>l B \<longmapsto> B" unfolding CastDual_def  by (simp add: cast_id)

lemma "=_\<nu>cast": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto
lemma [\<nu>intro']: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e N = N' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<longmapsto> \<tort_lbrace>x' \<tycolon> N'\<tort_rbrace>" unfolding Cast_def Premise_def by simp
lemma [\<nu>intro0]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x" unfolding Premise_def by simp
lemma [\<nu>intro]: " \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P2 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<heavy_comma>B) \<longmapsto> (A'\<heavy_comma>B') \<^bold>w\<^bold>i\<^bold>t\<^bold>h P1 \<and> P2"
  unfolding Cast_def by auto

lemma cast_trans: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> C \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<and> Q"
  unfolding Cast_def by auto
(* lemma dual_cast_fallback[\<nu>intro']: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<and> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t C \<longmapsto> C)" unfolding Cast_def by fast *)

theorem apply_cast: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> X\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H)) \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>w\<^bold>i\<^bold>t\<^bold>h P) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> Y\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p H) \<addition> P)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Cast_def by (auto 4 6)
theorem cast: "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  for T' :: "(heap \<times> 'a::lrep) set" unfolding Cast_def CurrentConstruction_def by auto

(* theorem proc_cast': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> A \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>w\<^bold>i\<^bold>t\<^bold>h Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A' \<longmapsto> B' \<brangle>"
  unfolding Procedure_def Cast_def by (auto 0 4) *)

lemma [\<nu>intro']: "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Intro_def .
lemma [\<nu>intro']: "\<^bold>d\<^bold>e\<^bold>s\<^bold>t \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>w\<^bold>i\<^bold>t\<^bold>h P" unfolding Dest_def .

subsection \<open>Conversion\<close>

(* definition AutoTag :: "bool \<Rightarrow> bool" ("\<^bold>a\<^bold>u\<^bold>t\<^bold>o _" [100] 99) where [\<nu>def]: "\<^bold>a\<^bold>u\<^bold>t\<^bold>o P \<longleftrightarrow> P"
lemma [\<nu>intro]: "[heap] \<^bold>c\<^bold>a\<^bold>s\<^bold>t U \<longmapsto> U' \<Longrightarrow> \<^bold>a\<^bold>u\<^bold>t\<^bold>o \<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> U \<longmapsto> U' \<brangle>"
  unfolding AutoTag_def Cast_def Procedure_def nop_def by auto *)
  
definition Conversion :: "('a::lrep \<longmapsto> 'b::lrep) \<Rightarrow> (heap\<times>'a) set \<Rightarrow> (heap\<times>'b) set \<Rightarrow> ( ('c::lrep) \<longmapsto> ('d::lrep)) \<Rightarrow> (heap\<times>'c) set \<Rightarrow> (heap\<times>'d) set \<Rightarrow> bool"
    ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)/ \<long_dobule_mapsto> _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)" [101,2,2,101,2,2] 100)
    where [\<nu>def]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> g \<blangle> U' \<longmapsto> V' \<brangle> \<longleftrightarrow>( \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> V' \<brangle> )"

lemma conversion: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f' \<blangle> U' \<longmapsto> V' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U' \<longmapsto> V' \<brangle>"
  for f :: " ('a::lrep) \<longmapsto> ('b::lrep)" and f' :: " ('c::lrep) \<longmapsto> ('d::lrep)" unfolding Conversion_def by fast

lemma [\<nu>intro0]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U \<longmapsto> V \<brangle>" unfolding Conversion_def by fast

lemma conversion_cast[\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<^bold>d\<^bold>u\<^bold>a\<^bold>l V \<longmapsto> V' \<^bold>w\<^bold>h\<^bold>e\<^bold>n Q \<Longrightarrow> (P \<Longrightarrow> Q) \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U' \<longmapsto> V'\<brangle>"
  unfolding Conversion_def Procedure_def Cast_def CastDual_def id_def
  by (metis Cast_def CurrentConstruction_def LooseStateTy_introByStrict LooseStateTy_upgrade cast)
(* lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> U \<brangle> \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> (g \<nuInstrComp> f) \<blangle> U' \<longmapsto> V\<brangle>"
  unfolding Conversion_def using instr_comp by fast *)

theorem apply_proc_conv: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> S' \<longmapsto> T' \<brangle> \<long_dobule_mapsto> g \<blangle> S \<longmapsto> T\<brangle>) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S' \<longmapsto> T' \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Conversion_def by auto

lemma conversion_trans: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n g \<blangle> Xg \<longmapsto> Yg \<brangle> \<long_dobule_mapsto> h \<blangle> Xh \<longmapsto> Yh \<brangle>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> Xf \<longmapsto> Yf \<brangle> \<long_dobule_mapsto> g \<blangle> Xg \<longmapsto> Yg \<brangle>
  \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> Xf \<longmapsto> Yf\<brangle> \<long_dobule_mapsto> h \<blangle> Xh \<longmapsto> Yh \<brangle>"
  unfolding Conversion_def by blast

subsection \<open>Heap\<close>

consts ResourceState :: " heap \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> bool" ("_ \<^bold>a\<^bold>t _ \<^bold>i\<^bold>s _ " [16,16,12] 11)
consts allocated :: " heap \<Rightarrow> 'a \<Rightarrow> bool"

translations "h \<^bold>a\<^bold>t resource \<^bold>i\<^bold>s x \<tycolon> T" \<rightleftharpoons> "h \<^bold>a\<^bold>t resource \<^bold>i\<^bold>s \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"

definition "addr_allocated heap addr \<longleftrightarrow> MemAddress addr \<in> dom heap"
adhoc_overloading allocated addr_allocated

(* lemma addr_allocated_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> addr_allocated h addr \<Longrightarrow> addr_allocated h' addr"
  unfolding addr_allocated_def by auto
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto *)
lemma [iff]: "addr_allocated (h(k \<mapsto> v)) addr \<longleftrightarrow> k = MemAddress addr \<or> addr_allocated h addr"
  and [iff]: "addr_allocated (h(k := None)) addr \<longleftrightarrow> k \<noteq> MemAddress addr \<and> addr_allocated h addr"
  unfolding addr_allocated_def by auto

definition MemAddrState :: "heap \<Rightarrow> nat memaddr \<Rightarrow> 'b::lrep set \<Rightarrow> bool"
  where "MemAddrState h addr S \<longleftrightarrow> addr_allocated h addr \<and> shallowize (the (h (MemAddress addr))) \<in> S"
adhoc_overloading ResourceState MemAddrState

(*lemma MemAddrState_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> MemAddrState h' addr S"
  unfolding MemAddrState_def addr_allocated_def by auto (metis \<nu>set_mono domI map_le_def option.sel) *)

lemma MemAddrState_I_neq[intro]: "k2 \<noteq> k \<Longrightarrow> MemAddrState h k2 S \<Longrightarrow> MemAddrState (h(MemAddress k := v)) k2 S"
  and MemAddrState_I_eq[intro]: "v' \<in> S \<Longrightarrow> MemAddrState (h(MemAddress k \<mapsto> deepize v')) k S"
  unfolding MemAddrState_def addr_allocated_def by auto

lemma MemAddrState_E[elim]:
  "MemAddrState h addr S \<Longrightarrow> (addr_allocated h addr \<Longrightarrow> Inhabited S \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding MemAddrState_def by auto
lemma MemAddrState_I:
  "addr_allocated h addr \<Longrightarrow> shallowize (the (h (MemAddress addr))) \<in> S \<Longrightarrow> MemAddrState h addr S"
  unfolding MemAddrState_def by auto

(* lemma MemAddrState_retained_N[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<nu>Independent S claim
    \<Longrightarrow> Alive k \<in> claim \<Longrightarrow> MemAddrState (h(k:=None)) addr S"
  unfolding MemAddrState_def \<nu>Independent_def by auto
lemma MemAddrState_retained_S[intro]:
  "k \<noteq> MemAddress addr \<Longrightarrow> MemAddrState h addr S \<Longrightarrow> \<nu>Independent S claim
    \<Longrightarrow> Write k \<in> claim \<Longrightarrow> MemAddrState (h(k \<mapsto> v)) addr S"
  unfolding MemAddrState_def \<nu>Independent_def by auto

*)


lemma MemAddrState_restrict_I1[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> a \<in> S \<Longrightarrow> h |` (MemAddress ` S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and MemAddrState_restrict_I2[intro]: "h \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> a \<notin> S \<Longrightarrow> h |` (- MemAddress ` S) \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def
  by auto (metis ComplI imageE option.sel resource_key.inject(1) restrict_map_def)

lemma MemAddrState_add_I1[intro]: " h1 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  and  MemAddrState_add_I2[intro]: " h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 ++ h2 \<^bold>a\<^bold>t a \<^bold>i\<^bold>s T "
  unfolding MemAddrState_def addr_allocated_def by (auto simp add: map_add_def disjoint_def split: option.split)
  

 subsubsection \<open>Auto construct & destruct\<close>

definition AutoConstruct :: " 'exp \<Rightarrow> ('a::lrep \<longmapsto> 'b::lrep) \<Rightarrow> (heap \<times> 'a) set \<Rightarrow> (heap \<times> 'b) set \<Rightarrow> bool "("\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t _/ \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<blangle>_/ \<longmapsto> _ \<brangle>)" [20,101,10,10] 100)
  where [\<nu>def]:"AutoConstruct exp f S T \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>"
lemma AutoConstruct: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> AutoConstruct exp f S T \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)" for exp :: "'exp"
  unfolding AutoConstruct_def using apply_proc .

(* lemma [simp]: "(Inhabited A \<and> Inhabited B) \<or> (Inhabited A' \<and> Inhabited B')
  \<Longrightarrow> (A\<heavy_comma>B) = (A'\<heavy_comma>B') \<longleftrightarrow> A = A' \<and> B = B'" unfolding Stack_Delimiter_def Inhabited_def by (auto simp add: times_eq_iff) 
lemma  [elim]: "(A\<heavy_comma>B) = (A'\<heavy_comma>B') \<Longrightarrow> (A = {} \<or> B = {} \<Longrightarrow> A' = {} \<or> B' = {} \<Longrightarrow> C) \<Longrightarrow> (A = A' \<Longrightarrow> B = B' \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Stack_Delimiter_def by (auto simp add: times_eq_iff)
*)


end
