(* KEEP IT SIMPLE AND STUPID *)

theory NuPrime \<comment> \<open>The Primary Theory of the \<nu>-System\<close>
  imports Main "HOL-Library.Monad_Syntax" NuHelpMath
  abbrevs "is" = "\<^bold>i\<^bold>s"
      and "as" = "\<^bold>a\<^bold>s"
      and "<and>" = "\<^bold>a\<^bold>n\<^bold>d"
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
      and "<claim>" = "\<^bold>c\<^bold>l\<^bold>a\<^bold>i\<^bold>m"
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
  (* and \<nu>address_def \<open>primitive definitions for unfolding in proofs for address\<close> *)
  and \<nu>post_construct and \<nu>auto_destruct
named_theorems typing_expn "expansion theorems for abstractions" and lrep_exps

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

definition ProtectorI :: "'a \<Rightarrow> 'a" where "ProtectorI x = x"
lemma [cong]: "ProtectorI X \<equiv> ProtectorI X" .

definition WorkingProtector :: "'a \<Rightarrow> 'a" where "WorkingProtector x \<equiv> x"

datatype 'a tree = Leaf | Node 'a \<open>'a tree\<close> \<open>'a tree\<close>

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

type_synonym msegment = nat
type_synonym addr_space = nat
  \<comment> \<open>Address space is a notion of the LLVM. The space 0 is the main memory of the device.
    Space other than 0 is specified depending on platform, which may represent addresses on remote devices like display card\<close>

datatype 'offset memaddr = memaddr (segment_of_addr: msegment) (offset_of_addr: 'offset ) (infixl "|+" 60)

abbreviation shift_addr :: " 'a::plus memaddr \<Rightarrow> 'a \<Rightarrow> 'a memaddr" (infixl "||+" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. x + delta) addr"
lemma memaddr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>base ofs. P (base  |+ ofs))" by (metis memaddr.exhaust)
lemma memaddr_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>base ofs. P (base  |+ ofs))" by (metis memaddr.exhaust)

datatype deep_model = DM_int nat nat | DM_pointer nat "nat memaddr" | DM_fusion deep_model deep_model
  | DM_record deep_model | DM_array "deep_model list" | DM_none

datatype resource_key = MemAddress "nat memaddr" | ChainDB_key nat
  \<comment> \<open>The write operation on address `addr` requires owning of resource `MemAddress addr`,
    while the dispose of that memory on `addr` requires both owning of resource `MemAddress addr`
      and `Dispose (MemAddress addr)`\<close>

datatype claim_key = Write resource_key | Alive resource_key
text \<open>When the post-condition claims `Write`, it grants the right to change the state of the resource, but may not to dispose it;
  when the post-condition claims `Alive`, it grants the right to dispose the resource, but may not to change;
  when the precondition claims `Write`, it requests to change the resource but not to dispose;
  when the precondition claims `Alive`, it requests to dispose the resource, particularly maybe a read-only resource.
  Most of the abstractions claim either `Alive` or both `Alive` and `Write`; it's rare for them to claim the `Write` only.
  However there is a case claiming the `Write` only, the WeakReference which states if the resource is still alive,
  the state would be something. \<close>

lemma resource_key_forall: "All P \<longleftrightarrow> (\<forall>addr. P (MemAddress addr)) \<and> (\<forall>n. P (ChainDB_key n))" by (metis resource_key.exhaust)
lemma resource_key_exists: "Ex P \<longleftrightarrow> (\<exists>addr. P (MemAddress addr)) \<or> (\<exists>n. P (ChainDB_key n))" by (metis resource_key.exhaust)
lemma claim_key_forall: "All P \<longleftrightarrow> (\<forall>k. P (Write k)) \<and> (\<forall>k. P (Alive k))" by (metis claim_key.exhaust)
lemma claim_key_exists: "Ex P \<longleftrightarrow> (\<exists>k. P (Write k)) \<or> (\<exists>k. P (Alive k))" by (metis claim_key.exhaust)

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

datatype llty = llty_int nat \<comment> \<open>int bits\<close> | llty_pointer nat \<comment> \<open>pointer space\<close> | llty_tup llty | llty_array llty nat | llty_nil | llty_fusion llty llty

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

type_synonym ('a,'b) \<nu> = " heap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool "

subsection \<open>The \<nu>-set\<close>

definition NuSet :: " (heap \<Rightarrow> 'a set) set " where "NuSet = {S. (\<forall>h h' p. h \<subseteq>\<^sub>m h' \<longrightarrow>  p \<in> S h \<longrightarrow> p \<in> S h')}"
typedef 'a \<nu>set = "NuSet :: (heap \<Rightarrow> 'a set) set"
  morphisms set_of_\<nu> Abs_\<nu>set
  unfolding NuSet_def
  proof show "(\<lambda>x. {}) \<in> {S. \<forall>h h' p. h \<subseteq>\<^sub>m h' \<longrightarrow> p \<in> S h \<longrightarrow> p \<in> S h'}" by simp qed

setup_lifting type_definition_\<nu>set

abbreviation In_\<nu>set :: " heap \<Rightarrow> 'a \<Rightarrow> 'a \<nu>set \<Rightarrow> bool " ( "[_] _ \<in>\<^sub>\<nu> _" [20,51,51] 50)
  where "[heap] x \<in>\<^sub>\<nu> S \<equiv> x \<in> set_of_\<nu> S heap"
abbreviation NotIn_\<nu>set :: " heap \<Rightarrow> 'a \<Rightarrow> 'a \<nu>set \<Rightarrow> bool " ( "[_] _ \<notin>\<^sub>\<nu> _" [20,51,51] 50)
  where "[heap] x \<notin>\<^sub>\<nu> S \<equiv> x \<notin> set_of_\<nu> S heap"

lemma \<nu>set_eq_iff: "M = N \<longleftrightarrow> (\<forall>h a. [h] a \<in>\<^sub>\<nu> M \<longleftrightarrow> [h] a \<in>\<^sub>\<nu> N)"
  by (simp only: set_of_\<nu>_inject [symmetric] fun_eq_iff set_eq_iff)

abbreviation Empty_\<nu>set :: "'a \<nu>set" ("\<emptyset>\<^sub>\<nu>") where "Empty_\<nu>set \<equiv> Abs_\<nu>set (\<lambda>_. {})"
lemma [simp]: "\<not>([h] p \<in>\<^sub>\<nu> \<emptyset>\<^sub>\<nu>)" by (simp add: Abs_\<nu>set_inverse NuSet_def)

subsection \<open>The \<nu>-type\<close>

subsubsection \<open>Definitions\<close>

(* ceq : INF *)

datatype ('a,'b) typing = typing 'b "('a,'b) \<nu>" (infix "\<tycolon>" 15) \<comment>\<open>shortcut keys "<ty>"\<close>
primrec nu_of :: "('a,'b) typing \<Rightarrow> ('a,'b) \<nu>" where "nu_of (x \<tycolon> N) = N"
primrec image_of :: "('a,'b) typing \<Rightarrow> 'b" where "image_of (x \<tycolon> N) = x"

definition Nu :: " ('a,'b) \<nu> \<Rightarrow> bool " where "Nu N \<longleftrightarrow> (\<forall>h h' p x. h \<subseteq>\<^sub>m h' \<longrightarrow>  N h p x \<longrightarrow> N h' p x)"

definition RepSet :: "('a,'b) typing \<Rightarrow> 'a \<nu>set" ("\<tort_lbrace> _ \<tort_rbrace>" [10] ) where "\<tort_lbrace> ty \<tort_rbrace> = Abs_\<nu>set (\<lambda>res. {p. case ty of (x \<tycolon> N) \<Rightarrow> Nu N \<and> N res p x })"
abbreviation Refining :: "heap \<Rightarrow> 'a \<Rightarrow> ('a,'b) \<nu> \<Rightarrow>  'b \<Rightarrow> bool" ("([_] _/ \<nuLinkL> _  \<nuLinkR>/ _)" [15, 27,15,27] 26) \<comment>\<open>shortcut keys "--<" and ">--"\<close>
  where  "([heap] p \<nuLinkL> N \<nuLinkR> x) \<equiv> [heap] p \<in>\<^sub>\<nu> \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
definition Inhabited :: " 'a \<nu>set \<Rightarrow> bool" where "Inhabited s \<equiv> (\<exists>h x. [h] x \<in>\<^sub>\<nu> s)"
abbreviation InhabitTyp :: " 'b \<Rightarrow> ('a::lrep,'b) \<nu> \<Rightarrow> bool" (infix "\<ratio>" 15)  \<comment>\<open>shortcut keys ":TY:"\<close>
  where  "(x \<ratio> N) \<equiv> Inhabited \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
text \<open>The @{term "x \<tycolon> N"} is a predication specifying concrete values,
  e.g. @{prop "[heap] a_concrete_int32 \<in>\<^sub>\<nu> \<tort_lbrace>(42::nat) \<tycolon> N 32\<tort_rbrace>"} and also "state \<in> State (\<tort_lbrace>42 \<tycolon> N\<tort_rbrace> \<times> \<tort_lbrace>24 \<tycolon> N\<tort_rbrace> \<times> \<cdots> )".
  It constitutes basic elements in specification.
  The @{prop "[heap] p \<nuLinkL> N \<nuLinkR> x"} as the abbreviation of $p \<in> (x \<tycolon> N)$ is an abstraction between concrete value @{term p} and
  abstracted {\it image} @{term x} via the \<nu>-{\it abstractor} @{term N} which defines the abstraction relationship itself.
  The next @{prop "x \<ratio> N"} is a proposition stating @{term x} is an image of abstractor @{term N} and therefore
  the \<nu>-type @{term "x \<tycolon> N"} is inhabited. Basically it is used to derive implicated conditions of images,
  e.g. @{prop "(42 \<ratio> N 32) \<Longrightarrow> 42 < 2^32"}\<close>

lemma Refining_ex: "[heap] p \<nuLinkL> R \<nuLinkR> x \<longleftrightarrow> Nu R \<and> R heap p x"
  unfolding RepSet_def by (auto simp add: Abs_\<nu>set_inverse[unfolded NuSet_def, simplified] Nu_def)

(* lemma [elim!,\<nu>elim]: "Inhabited (U \<times> V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> PROP C) \<Longrightarrow> PROP C" unfolding Inhabited_def by auto *)
lemma [intro]: "[heap] x \<in>\<^sub>\<nu> S \<Longrightarrow> Inhabited S" unfolding Inhabited_def by auto
lemma Inhabited_E: "Inhabited S \<Longrightarrow> (\<And>x heap. [heap] x \<in>\<^sub>\<nu> S \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto


lemma [dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> h k = Some v \<Longrightarrow> h' k = Some v"
  by (metis domI map_le_def)
lemma \<nu>set_mono[dest]: "h \<subseteq>\<^sub>m h' \<Longrightarrow> [h] p \<in>\<^sub>\<nu> S \<Longrightarrow> [h'] p \<in>\<^sub>\<nu> S" by transfer (auto simp add: NuSet_def)
lemma \<nu>set_mono_1[dest]: "k \<notin> dom h \<Longrightarrow> [h] p \<in>\<^sub>\<nu> S \<Longrightarrow> [h(k := v)] p \<in>\<^sub>\<nu> S" subgoal premises prems proof -
    have a: "h \<subseteq>\<^sub>m h(k := v)" unfolding map_le_def using prems by auto
    show ?thesis using a[THEN \<nu>set_mono, OF prems(2)] .
  qed done

subsubsection \<open>Properties\<close>

definition \<nu>Zero :: "('a::{zero,lrep},'b) \<nu> \<Rightarrow> 'b \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Zero N x \<longleftrightarrow> (\<forall>res. [res] 0 \<nuLinkL> N \<nuLinkR> x )"
definition \<nu>Equal :: "('a::{lrep,ceq}, 'b) \<nu> \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Equal N can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 heap.
    can_eq x1 x2 \<and> ([heap] p1 \<nuLinkL> N \<nuLinkR> x1) \<and> ([heap] p2 \<nuLinkL> N \<nuLinkR> x2) \<longrightarrow> ceqable heap p1 p2 \<and> (ceq p1 p2 = eq x1 x2))"

subsubsection \<open>Retaining\<close>

definition disjoint (infix "\<perpendicular>" 60) where "disjoint A B \<equiv> (A \<inter> B = {})"
definition involve_claim :: " claim_key set \<Rightarrow> claim_key set \<Rightarrow> bool" (infix "<involve>" 50)
  where "involve_claim = (\<subseteq>)"

lemma disjoint_rew: "A \<perpendicular> B \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> a \<in> B \<longrightarrow> False)" unfolding disjoint_def by auto
lemma disjoint_rew2: "A \<perpendicular> B \<longleftrightarrow> (\<forall>a. a \<in> B \<longrightarrow> a \<notin> A)" unfolding disjoint_def by auto

inductive heap_extension :: "claim_key set \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" where 
  heap_extension_0[intro]: "heap_extension claim heap heap " |
  heap_extension_S[intro]: "heap \<subseteq>\<^sub>m heap' \<Longrightarrow> heap_extension claim h heap \<Longrightarrow> heap_extension claim h heap' " |
  heap_extension_W[intro]: "Write k \<in> claim \<Longrightarrow> heap_extension claim heap heap' \<Longrightarrow> heap_extension claim heap (heap'(k \<mapsto> v))" |
  heap_extension_A[intro]: "Alive k \<in> claim \<Longrightarrow> heap_extension claim heap heap' \<Longrightarrow> heap_extension claim heap (heap'(k := None))"

lemma heap_extension_S2: "h \<subseteq>\<^sub>m h' \<Longrightarrow> heap_extension claim h' heap \<Longrightarrow> heap_extension claim h heap"
  by (rotate_tac 1, induct rule: heap_extension.induct) auto

definition Retained :: " 'a \<nu>set \<Rightarrow> claim_key set \<Rightarrow> heap \<Rightarrow> 'a \<Rightarrow> bool "
  where "Retained S claim heap p \<longleftrightarrow>
    (\<forall>heap'. heap_extension claim heap heap' \<longrightarrow> [heap'] p \<in>\<^sub>\<nu> S) "

lemma Retained_subset_heap: "h \<subseteq>\<^sub>m h' \<Longrightarrow> Retained S claim h p \<Longrightarrow> Retained S claim h' p"
  unfolding Retained_def using heap_extension_S2 by auto

text \<open>All resources the abstraction claims in any cases\<close>
definition \<nu>Resources_of_set :: " 'a \<nu>set \<Rightarrow> claim_key set \<Rightarrow> bool "
  where [\<nu>def]: "\<nu>Resources_of_set S rcss \<longleftrightarrow>
    (\<forall>key heap p. [heap] p \<in>\<^sub>\<nu> S \<longrightarrow> Alive key \<notin> rcss \<longrightarrow> [heap(key := None)] p \<in>\<^sub>\<nu> S) \<and>
    (\<forall>key heap p. [heap] p \<in>\<^sub>\<nu> S  \<longrightarrow> Write key \<notin> rcss \<longrightarrow> (\<forall>v. [heap(key := Some v)] p \<in>\<^sub>\<nu> S))"
definition \<nu>Resources :: " ('a::lrep, 'b) \<nu> \<Rightarrow> ('b \<Rightarrow> claim_key set) \<Rightarrow> bool "
  where [\<nu>def]: "\<nu>Resources T rcss \<longleftrightarrow> (\<forall>x. \<nu>Resources_of_set \<tort_lbrace> x \<tycolon> T \<tort_rbrace> (rcss x))"

lemma \<nu>Resources_of_set_retained:
      "\<nu>Resources_of_set S rcss \<Longrightarrow> rcss \<perpendicular> claim \<Longrightarrow> [heap] p \<in>\<^sub>\<nu> S \<Longrightarrow> Retained S claim heap p"
  unfolding \<nu>Resources_of_set_def Retained_def disjoint_rew2
    apply auto subgoal for heap apply (rotate_tac -1) by (induct rule: heap_extension.induct) auto done
lemma \<nu>Resources_retained:
      "\<nu>Resources T rcss \<Longrightarrow> rcss x \<perpendicular> claim \<Longrightarrow> [heap] p \<nuLinkL> T \<nuLinkR> x \<Longrightarrow> heap_extension claim heap heap' \<Longrightarrow> [heap'] p \<nuLinkL> T \<nuLinkR> x"
  unfolding \<nu>Resources_def by (meson Retained_def \<nu>Resources_of_set_retained)

text \<open>Any resources the abstraction depends on in all cases\<close>
definition \<nu>Dependency_of_set  :: " 'a \<nu>set \<Rightarrow> claim_key set \<Rightarrow> bool "
  where "\<nu>Dependency_of_set S rcss \<longleftrightarrow>
    (\<forall>heap p key. [heap] p \<in>\<^sub>\<nu> S \<longrightarrow> Alive key \<in> rcss \<longrightarrow> [heap(key := None)] p \<notin>\<^sub>\<nu> S) \<and>
    (\<forall>heap p key. [heap] p \<in>\<^sub>\<nu> S \<longrightarrow> Write key \<in> rcss \<longrightarrow> (\<exists>v. [heap(key := Some v)] p \<notin>\<^sub>\<nu> S))"
definition \<nu>Dependency :: " ('a,'b) \<nu> \<Rightarrow> ('b \<Rightarrow> claim_key set) \<Rightarrow> bool "
  where "\<nu>Dependency N rcss \<longleftrightarrow> (\<forall>x. \<nu>Dependency_of_set \<tort_lbrace> x \<tycolon> N \<tort_rbrace> (rcss x))"

lemma \<nu>Dependency_of_set_retained:
    "\<nu>Dependency_of_set S rcss \<Longrightarrow> [heap] p \<in>\<^sub>\<nu> S \<Longrightarrow> Retained S claim heap p \<Longrightarrow> rcss \<perpendicular> claim"
  unfolding \<nu>Dependency_of_set_def Retained_def disjoint_rew claim_key_forall by auto blast


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
lemma [simp]: "[heap] x \<in>\<^sub>\<nu> Named name S \<longleftrightarrow> [heap] x \<in>\<^sub>\<nu> S" unfolding Named_def ..
lemma [\<nu>intro]: "\<nu>Resources_of_set S rcss \<Longrightarrow> \<nu>Resources_of_set (Named name S) rcss"
  unfolding Named_def by simp
lemma [\<nu>intro]: "\<nu>Dependency_of_set S rcss \<Longrightarrow> \<nu>Dependency_of_set (Named name S) rcss"
  unfolding Named_def by simp

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

subsubsection \<open>Delimiter operator\<close>

definition Stack_Delimiter :: " ('a :: stack) \<nu>set \<Rightarrow> ('b :: lrep) \<nu>set \<Rightarrow> ('b \<times> 'a) \<nu>set " ( "(2_/ \<heavy_comma> _)" [14,15] 14)
  where "Stack_Delimiter B A = Abs_\<nu>set (\<lambda>heap. set_of_\<nu> A heap \<times> set_of_\<nu> B heap) "
translations "R \<heavy_comma> x \<tycolon> N" == "R \<heavy_comma> \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
  "x \<tycolon> N \<heavy_comma> R" == "\<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<heavy_comma> R"

lemma [simp]: "[heap] (a,b) \<in>\<^sub>\<nu> (B \<heavy_comma> A) \<longleftrightarrow> [heap] a \<in>\<^sub>\<nu> A \<and> [heap] b \<in>\<^sub>\<nu> B" unfolding Stack_Delimiter_def by transfer (auto simp add: NuSet_def Abs_\<nu>set_inverse)
(* lemma [intro]: "[heap] a \<in>\<^sub>\<nu> A \<Longrightarrow> [heap] b \<in>\<^sub>\<nu> B \<Longrightarrow> [heap] (a,b) \<in>\<^sub>\<nu> (B \<heavy_comma> A)" by simp
lemma [elim]: "[heap] ab \<in>\<^sub>\<nu> (B \<heavy_comma> A) \<Longrightarrow> (\<And>a b. ab = (a,b) \<Longrightarrow> [heap] a \<in>\<^sub>\<nu> A \<Longrightarrow> [heap] b \<in>\<^sub>\<nu> B \<Longrightarrow> C) \<Longrightarrow> C" by (cases ab) simp *)
lemma [elim!,\<nu>elim]: "Inhabited (U\<heavy_comma>V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

subsubsection \<open>Tag: End_of_Contextual_Stack\<close>

definition End_of_Contextual_Stack :: " 'a \<Rightarrow> 'a " ("\<^bold>E\<^bold>N\<^bold>D") where [\<nu>def]: "End_of_Contextual_Stack x = x" \<comment> \<open>A tag for printing sugar\<close>
lemmas End_of_Contextual_Stack_rew = End_of_Contextual_Stack_def[THEN eq_reflection]
lemma [elim,\<nu>elim]: "Inhabited (End_of_Contextual_Stack S) \<Longrightarrow> C \<Longrightarrow> C" .

subsection \<open>The \<nu>-system VM and Procedure construction structures\<close>

datatype 'a state = Success heap 'a | Fail | PartialCorrect
text\<open> The basic state of the \<nu>-system virtual machine is represented by type @{typ "('a::lrep) state"}.
  The valid state `Success` essentially has two major form, one without registers and another one with them,
      \<^item> "StatOn (x1, x2, \<cdots>, xn, void)",
  where @{term "(x1, x2, \<cdots>, xn, void)"} represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term PartialCorrect} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term PartialCorrect} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>

declare state.split[split]

subsubsection \<open>Types specifying states\<close>

definition StrictStateTy :: " ('a::lrep) \<nu>set \<Rightarrow> 'a state set" ("\<S_S> _" [56] 55)
  where "\<S_S> T = {s. case s of Success heap x \<Rightarrow> Heap heap \<and> [heap] x \<in>\<^sub>\<nu> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"
definition LooseStateTy :: " ('a::lrep) \<nu>set \<Rightarrow> 'a state set" ("\<S> _" [56] 55)
  where "\<S> T = {s. case s of Success heap x \<Rightarrow> Heap heap \<and> [heap] x \<in>\<^sub>\<nu> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma [simp]: "Success heap x \<in> \<S_S> T \<equiv> Heap heap \<and> [heap] x \<in>\<^sub>\<nu> T" and [simp]: "\<not> (Fail \<in> \<S_S> T)" and [simp]: "\<not> (PartialCorrect \<in> \<S_S> T)"
  and [simp]: "Success heap x \<in> \<S> T \<equiv> Heap heap \<and> [heap] x \<in>\<^sub>\<nu> T" and [simp]: "\<not> (Fail \<in> \<S> T)" and [simp]: "(PartialCorrect \<in> \<S> T)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
(* lemma [dest]: "s \<in> \<S_S> T \<Longrightarrow> Inhabited T" unfolding Inhabited_def by (cases s) auto *)
    \<comment>\<open>The inhabited property can be inferred from @{term StrictStateTy} only rather than @{term LooseStateTy}. \<close>
lemma [elim]: "s \<in> \<S_S> T \<Longrightarrow> (\<And>x h. Heap h \<Longrightarrow> s = Success h x \<Longrightarrow> [h] x \<in>\<^sub>\<nu> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma [intro]: "Heap h \<Longrightarrow> [h] x \<in>\<^sub>\<nu> T \<Longrightarrow> Success h x \<in> \<S_S> T" by simp
lemma [elim]: "s \<in> \<S> T \<Longrightarrow> (\<And>x h. Heap h \<Longrightarrow> s = Success h x \<Longrightarrow> [h] x \<in>\<^sub>\<nu> T \<Longrightarrow> C) \<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma [intro]: "Heap h \<Longrightarrow> [h] x \<in>\<^sub>\<nu> T \<Longrightarrow> Success h x \<in> \<S> T" and [intro]: "PartialCorrect \<in> \<S> T" by simp_all
lemma LooseStateTy_upgrade: "s \<in> \<S> T \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> \<S_S> T" by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> \<S_S> T \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> \<S_S> T) \<Longrightarrow> s \<in> \<S> T" by (cases s) auto

subsubsection \<open>\<nu>-Procedure\<close>

type_synonym ('a,'b) proc = "heap \<Rightarrow> 'a \<Rightarrow> 'b state" (infix "\<longmapsto>" 0)
definition Procedure :: "('a \<longmapsto> 'b) \<Rightarrow> ('a::lrep) \<nu>set \<Rightarrow> ('b::lrep) \<nu>set \<Rightarrow> bool" ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ \<blangle>(2 _/  \<longmapsto>  _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]:"Procedure f T U \<longleftrightarrow> (\<forall>a h. Heap h \<longrightarrow> [h] a \<in>\<^sub>\<nu> T \<longrightarrow> f h a \<in> \<S> U)"
definition Map :: " 'a \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> ('a \<Rightarrow> 'b) set " where "Map A B = {f. \<forall>a h. [h] a \<in>\<^sub>\<nu> A \<longrightarrow> [h] f a \<in>\<^sub>\<nu> B }"
definition Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<blangle>(2 _/ \<longmapsto> _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle> \<equiv> \<forall>a h. [h] a \<in>\<^sub>\<nu> T \<longrightarrow> [h] f a \<in>\<^sub>\<nu> U"
(* lemma [intro]: "(\<And>x h. x \<in> T h \<Longrightarrow> f x \<in> U h) \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle>" by auto *)
(* lemma [simp]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> \<S> U \<brangle> \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> T \<longmapsto> U \<brangle>" unfolding \<nu>def by fast  *)

subsection \<open>Primitive operations and instructions required in the system\<close>

subsubsection \<open>Elementary instructions\<close>

definition bind :: " ('a::lrep) state \<Rightarrow> ( 'a \<longmapsto> 'b) \<Rightarrow> ('b::lrep) state " \<comment>\<open>monadic bind\<close>
  where "bind s f = (case s of Success h x \<Rightarrow> f h x | Fail \<Rightarrow> Fail | PartialCorrect \<Rightarrow> PartialCorrect)"
definition instr_comp :: "(('a::lrep) \<longmapsto> ('b::lrep)) \<Rightarrow> ( 'b \<longmapsto> ('c::lrep)) \<Rightarrow> 'a \<longmapsto> 'c"  ("_ \<nuInstrComp>/ _" [75,76] 75) 
  where "instr_comp f g heap s = bind (f heap s) g"
definition nop :: " ('a::lrep) \<longmapsto> 'a" where "nop = Success" \<comment>\<open>the instruction `no-operation`\<close>

lemma nop_\<nu>proc: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> T \<longmapsto> T \<brangle>" unfolding nop_def Procedure_def by auto
lemma instr_comp[intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> B \<longmapsto> C \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> g) \<blangle> A \<longmapsto> C \<brangle>"
  unfolding instr_comp_def Procedure_def bind_def by auto fastforce+


subsection \<open>Top-level Construction Structures\<close>

subsubsection \<open>Construction Context & Code block\<close>

definition CurrentConstruction :: " ('a::lrep) state \<Rightarrow> 'a \<nu>set \<Rightarrow> bool " ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,11] 10)
  where "CurrentConstruction s S \<longleftrightarrow> s \<in> \<S_S> S"
definition PendingConstruction :: " (('a::lrep) \<longmapsto> ('b::lrep)) \<Rightarrow> 'a state \<Rightarrow> 'b \<nu>set \<Rightarrow> bool " ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,5] 4)
  where "PendingConstruction f s S \<longleftrightarrow> bind s f \<in> \<S> S"

lemma [elim!,\<nu>elim]: "CurrentConstruction s S \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> C" unfolding CurrentConstruction_def by auto

definition CodeBlock :: " ('a::lrep) state \<Rightarrow> heap \<times> ('b::lrep) => 'b \<nu>set \<Rightarrow> ('b \<longmapsto> 'a) \<Rightarrow> bool" where
  CodeBlock_def: "CodeBlock stat arg ty prog \<longleftrightarrow> (Heap (fst arg) \<and> [fst arg] (snd arg) \<in>\<^sub>\<nu> ty \<and> prog (fst arg) (snd arg) = stat \<and> stat \<noteq> PartialCorrect)"
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
lemma CodeBlock_unabbrev: "CodeBlock v arg ty prog \<Longrightarrow> (v \<equiv> ProtectorI (prog (fst arg) (snd arg)))"
  unfolding CodeBlock_def ProtectorI_def by (rule eq_reflection) fast
lemma CodeBlock_abbrev: "CodeBlock v arg ty prog \<Longrightarrow> ProtectorI (prog (fst arg) (snd arg)) \<equiv> v"
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
  from prems(2) have sa: "Heap (fst a) \<and> [fst a] snd a \<in>\<^sub>\<nu> S \<and> f (fst a) (snd a) = f (fst a) (snd a) \<and> f (fst a) (snd  a) \<noteq> PartialCorrect" 
    by (cases "f (fst a) (snd a)") (auto simp add: bind_def)
  note th = prems(1)[OF sa, simplified prems(2)[THEN conjunct1]]
  from th[THEN SpecTop_focus] show "s' \<in> \<S_S> T" using prems(2) by (blast intro: LooseStateTy_upgrade)
  from th[THEN SpecTop_facts] show "PROP L" .
qed done

lemma codeblock_export: "PROP Pure.prop (\<And>s. CodeBlock s a T f \<Longrightarrow> PROP C) \<Longrightarrow> PROP Pure.prop (\<And>s. CodeBlock s a T (f \<nuInstrComp> g) \<Longrightarrow> PROP C)"
  unfolding CodeBlock_def prop_def instr_comp_def proof -
  assume A[of "f (fst a) (snd a)", simplified]: "(\<And>s. Heap (fst a) \<and> [fst a] snd a \<in>\<^sub>\<nu> T \<and> f (fst a) (snd a) = s \<and> s \<noteq> PartialCorrect \<Longrightarrow> PROP C)"
  fix s show "Heap (fst a) \<and> [fst a] snd a \<in>\<^sub>\<nu> T \<and> bind (f (fst a) (snd a)) g = s \<and> s \<noteq> PartialCorrect \<Longrightarrow> PROP C" proof -
    assume [unfolded bind_def]: "Heap (fst a) \<and> [fst a] snd a \<in>\<^sub>\<nu> T \<and> bind (f (fst a) (snd a)) g = s \<and> s \<noteq> PartialCorrect"
    then have "Heap (fst a) \<and> [fst a] snd a \<in>\<^sub>\<nu> T \<and> f (fst a) (snd a) \<noteq> PartialCorrect" by auto
    from this[THEN A] show "PROP C" .
  qed
qed

theorem start_proc:
  "CodeBlock s a S nop \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S"
  for S :: " ('a::lrep) \<nu>set" and a :: "heap \<times> 'a" and s :: "'a state"
  unfolding nop_def CodeBlock_def CurrentConstruction_def by auto

theorem finish_proc: "(\<And>a s. CodeBlock s a S f \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T))
  \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>" for S :: "('a::lrep) \<nu>set" and  T :: "('b::lrep) \<nu>set"
  unfolding CodeBlock_def Procedure_def
  subgoal premises rule apply (rule,rule,rule,rule) subgoal premises a for a h proof -
    note rule[of "(h,a)" "f h a", unfolded CurrentConstruction_def, simplified] 
    then show "f h a \<in> \<S> T" unfolding instr_comp_def bind_def
      using LooseStateTy_introByStrict a by (cases "f h a") auto
  qed done done

theorem start_block:
  "((PROP X) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<Longrightarrow>
      CodeBlock s a U nop \<Longrightarrow>
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)"
  for U :: " ('a::lrep) \<nu>set" and V :: "('b::lrep) \<nu>set" and s :: " 'a state" and a :: "heap \<times> 'a"
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

definition ExTyp :: "('a \<Rightarrow> 'b \<nu>set) \<Rightarrow> 'b \<nu>set" (binder "\<exists>* " 10)
  where   "ExTyp T = Abs_\<nu>set (\<lambda>h. {x. (\<exists>z. [h] x \<in>\<^sub>\<nu> T z)})"
notation ExTyp (binder "\<exists>\<^sup>\<nu> " 10)
  \<comment> \<open>which represents there exists some \<nu>-images (or rarely abstractors) subject to the typing.
    And then the image subjecting the typing could be fixed as a local variable by the \<nu>-obtain command. \<close>

lemma [simp]: "[heap] x \<in>\<^sub>\<nu> ExTyp T \<longleftrightarrow> (\<exists>z. [heap] x \<in>\<^sub>\<nu> T z)" unfolding ExTyp_def proof -
  have a1: "(\<lambda>h. {x. \<exists>z. [h] x \<in>\<^sub>\<nu> T z}) \<in> NuSet" unfolding NuSet_def by auto
  show " ([heap] x \<in>\<^sub>\<nu> Abs_\<nu>set (\<lambda>h. {x. \<exists>z. [h] x \<in>\<^sub>\<nu> T z})) = (\<exists>z. [heap] x \<in>\<^sub>\<nu> T z)"
    unfolding a1[THEN Abs_\<nu>set_inverse] by simp
qed
lemma [simp]: "x \<in> \<S> (ExTyp T) \<longleftrightarrow> (\<exists>z. x \<in> \<S> (T z))" by (auto 4 3)
lemma [simp]: "x \<in> \<S_S> (ExTyp T) \<longleftrightarrow> (\<exists>z. x \<in> \<S_S> (T z))" by (auto 4 3)
lemma [simp]: "(ExTyp A \<heavy_comma> R) = (\<exists>* x. (A x \<heavy_comma> R))" by (simp add: \<nu>set_eq_iff)
lemma [simp]: "(S\<heavy_comma> ExTyp T) = (\<exists>* z. (S \<heavy_comma> T z))" by (simp add: \<nu>set_eq_iff)
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

definition AddtionTy :: " 'a \<nu>set \<Rightarrow> bool \<Rightarrow> 'a \<nu>set " (infixl "\<addition>" 50)
  where " (T \<addition> P) = Abs_\<nu>set (\<lambda>h. {x. [h] x \<in>\<^sub>\<nu> T \<and> P})"
lemma [simp]: "T \<addition> True = T" unfolding AddtionTy_def \<nu>set_eq_iff by transfer (simp add: Abs_\<nu>set_inverse )
lemma [simp]: "[h] x \<in>\<^sub>\<nu> (T \<addition> P) \<longleftrightarrow> [h] x \<in>\<^sub>\<nu> T \<and> P" unfolding AddtionTy_def by transfer (simp add: Abs_\<nu>set_inverse NuSet_def)
(* lemma [intro]: "P \<Longrightarrow> [h] x \<in>\<^sub>\<nu> T \<Longrightarrow> [h] x \<in>\<^sub>\<nu> (T \<addition> P)" by simp
lemma [elim]: "[h] x \<in>\<^sub>\<nu> (T \<addition> P) \<Longrightarrow> ([h] x \<in>\<^sub>\<nu> T \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C" by simp*)
lemma [simp]: "(R \<heavy_comma> T \<addition> P) = ((R \<heavy_comma> T) \<addition> P)" by (auto simp add: \<nu>set_eq_iff)
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

definition Cast :: " 'a \<nu>set \<Rightarrow> 'a \<nu>set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _/ \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e _)" [2,2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P) \<longleftrightarrow> (\<forall>x heap. [heap] x \<in>\<^sub>\<nu> A \<longrightarrow> [heap ]x \<in>\<^sub>\<nu> B \<and> P)"
consts SimpleCast :: " 'a \<nu>set \<Rightarrow> 'a \<nu>set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
translations "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B)" == "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e CONST True)"
translations "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> X \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P"
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> x \<tycolon> X \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" == "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> \<tort_lbrace> x \<tycolon> X \<tort_rbrace> \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P"
(* abbreviation SimpleCast :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _)" [2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B) \<equiv> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e True)" *)
(* lemma CastE[elim]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> (\<not> Inhabited A \<Longrightarrow> C) \<Longrightarrow> (Inhabited A \<Longrightarrow> Inhabited B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C"
   unfolding Cast_def Inhabited_def by (auto intro: Inhabited_subset)
lemma CastI[intro]: "Inhabited A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P"
  and [intro]: "\<not> Inhabited A \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P" unfolding Cast_def Inhabited_def by auto *)
lemma [\<nu>intro0]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A" unfolding Cast_def by fast
lemma "=_\<nu>cast": "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N" unfolding Cast_def by auto
lemma [\<nu>intro']: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e N = N' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x' \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t \<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<longmapsto> \<tort_lbrace>x' \<tycolon> N'\<tort_rbrace>" unfolding Cast_def Premise_def by simp
lemma [\<nu>intro0]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e x = x" unfolding Premise_def by simp
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> A' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P1 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P2 \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A\<heavy_comma>B) \<longmapsto> (A'\<heavy_comma>B') \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P1 \<and> P2"
  unfolding Cast_def by auto

theorem apply_cast: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> X)) \<Longrightarrow> (\<^bold>c\<^bold>a\<^bold>s\<^bold>t X \<longmapsto> Y \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P) \<Longrightarrow> (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (R \<heavy_comma> Y) \<addition> P)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Cast_def by (auto 4 6)
theorem cast: "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t T \<longmapsto> T' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T' "
  for T' :: "('a::lrep) \<nu>set" unfolding Cast_def CurrentConstruction_def by auto

theorem proc_cast': "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A' \<longmapsto> A \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t B \<longmapsto> B' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A' \<longmapsto> B' \<brangle>"
  unfolding Procedure_def Cast_def by (auto 0 4)


subsection \<open>Conversion\<close>

definition AutoTag :: "bool \<Rightarrow> bool" ("\<^bold>a\<^bold>u\<^bold>t\<^bold>o _" [100] 99) where [\<nu>def]: "\<^bold>a\<^bold>u\<^bold>t\<^bold>o P \<longleftrightarrow> P"
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U \<longmapsto> U' \<Longrightarrow> \<^bold>a\<^bold>u\<^bold>t\<^bold>o \<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> U \<longmapsto> U' \<brangle>"
  unfolding AutoTag_def Cast_def Procedure_def nop_def by auto
  
definition Conversion :: "( ('a::lrep) \<longmapsto> ('b::lrep)) \<Rightarrow> 'a \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> ( ('c::lrep) \<longmapsto> ('d::lrep)) \<Rightarrow> 'c \<nu>set \<Rightarrow> 'd \<nu>set \<Rightarrow> bool"
    ("\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)/ \<long_dobule_mapsto> _/ (2\<blangle> _/ \<longmapsto> _ \<brangle>)" [101,2,2,101,2,2] 100)
  where [\<nu>def]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> g \<blangle> U' \<longmapsto> V' \<brangle> \<longleftrightarrow>( \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> V' \<brangle> )"
lemma conversion: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f' \<blangle> U' \<longmapsto> V' \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> V \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U' \<longmapsto> V' \<brangle>"
  for f :: " ('a::lrep) \<longmapsto> ('b::lrep)" and f' :: " ('c::lrep) \<longmapsto> ('d::lrep)" unfolding Conversion_def by fast
lemma [\<nu>intro]: "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U \<longmapsto> V \<brangle>" unfolding Conversion_def by fast
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t U' \<longmapsto> U \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t V \<longmapsto> V' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> f \<blangle> U' \<longmapsto> V'\<brangle>"
  unfolding Conversion_def Procedure_def Cast_def  by (auto 0 4)
lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> U' \<longmapsto> U \<brangle> \<Longrightarrow> \<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> U \<longmapsto> V \<brangle> \<long_dobule_mapsto> (g \<nuInstrComp> f) \<blangle> U' \<longmapsto> V\<brangle>"
  unfolding AutoTag_def Conversion_def using instr_comp by fast

theorem apply_proc_conv: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> (\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n f \<blangle> S' \<longmapsto> T' \<brangle> \<long_dobule_mapsto> g \<blangle> S \<longmapsto> T\<brangle>) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S' \<longmapsto> T' \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp Conversion_def by auto


subsection \<open>Resource  Claim\<close>

named_theorems disj_intro and disj_intro0 and disj_elim and disj_dest and disj_simp


subsubsection \<open>Preliminary math\<close>

(* lemma "S \<subseteq> S' \<Longrightarrow> X \<perpendicular> S \<Longrightarrow> fresh \<perpendicular> dom h'" *)
(* lemma [simp]: "Retained T (claim1 \<union> claim2) h p \<longleftrightarrow> Retained T claim1 h p \<and> Retained T claim2 h p"
  unfolding Retained_def by auto *)

subsubsection \<open>Abstractor\<close>

(* definition Fresh :: " ('a::lrep) \<nu>set \<Rightarrow> resource_key set \<Rightarrow> ('a::lrep) \<nu>set " (infix "<Fresh>" 60)
  where "Fresh S fresh = Abs_\<nu>set (\<lambda>h. {p. fresh \<perpendicular> (dom h) \<and> [h] p \<in>\<^sub>\<nu> S})"
thm NuSet_def
lemma [simp]: "[h] p \<in>\<^sub>\<nu> Fresh T fresh \<longleftrightarrow> fresh \<perpendicular> (dom h) \<and> [h] p \<in>\<^sub>\<nu> T"
  unfolding Fresh_def proof -
  have a1: "(\<lambda>h. {p. fresh \<perpendicular> dom h \<and> [h] p \<in>\<^sub>\<nu> T}) \<in> NuSet" unfolding NuSet_def by auto
  by (auto 4 3 simp add: Abs_\<nu>set_inverse NuSet_def) *)

definition Claim :: " ('a::lrep) \<nu>set \<Rightarrow> claim_key set \<Rightarrow> ('a::lrep) \<nu>set " (infix "<Claim>" 60)
  where "Claim S claim = Abs_\<nu>set (\<lambda>h. {p. Retained S claim h p \<and> [h] p \<in>\<^sub>\<nu> S})"

lemma heap_extension_trans: "heap_extension claim h2 h3 \<Longrightarrow> heap_extension claim h1 h2 \<Longrightarrow> heap_extension claim h1 h3"
  by (induct  rule: heap_extension.induct) auto
lemma heap_extension_claim_subset:"heap_extension claim h h' \<Longrightarrow> claim \<subseteq> claim' \<Longrightarrow> heap_extension claim' h h' "
  by (induct rule: heap_extension.induct) auto

lemma heap_extension_updt: "heap_extension claim h h' \<Longrightarrow> heap_extension claim (h(k:=v)) (h'(k:=v))" 
  by (induct rule: heap_extension.induct)
    (metis map_le_upd fun_upd_twist fun_upd_upd heap_extension_0 heap_extension_W heap_extension_A heap_extension_S)+

lemma heap_extension_union:
  "heap_extension (claim1 \<union> claim2) h h' \<longleftrightarrow> (\<exists>hh. heap_extension claim1 h hh \<and> heap_extension claim2 hh h')"
  apply rule subgoal
    by (induct claim \<equiv> "claim1 \<union> claim2" h h' rule: heap_extension.induct) (auto intro: heap_extension_updt)
    by (auto intro: heap_extension_claim_subset heap_extension_trans) 

lemma [simp]: "[h] p \<in>\<^sub>\<nu> Claim T claim \<longleftrightarrow> Retained T claim h p \<and> [h] p \<in>\<^sub>\<nu> T"
  unfolding Claim_def proof -
  have a1: " (\<lambda>h. {p. Retained T claim h p \<and> [h] p \<in>\<^sub>\<nu> T})  \<in> NuSet"
    unfolding NuSet_def by (auto 4 4 simp add: Retained_def intro: heap_extension_trans)
  show "([h] p \<in>\<^sub>\<nu> Abs_\<nu>set (\<lambda>h. {p. Retained T claim h p \<and> [h] p \<in>\<^sub>\<nu> T})) = (Retained T claim h p \<and> [h] p \<in>\<^sub>\<nu> T)"
    unfolding a1[THEN Abs_\<nu>set_inverse] by simp
qed

lemma "\<nu>Resources_of_set B rcssB \<Longrightarrow> disjoint rcssB claim \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> Claim A claim \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (A \<heavy_comma> B) \<longmapsto> Claim (A \<heavy_comma> B) claim"
  unfolding Cast_def by (auto simp add: Retained_def \<nu>Resources_of_set_retained[unfolded Retained_def])

lemma "\<nu>Dependency_of_set B rcssB \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t Claim A claim \<longmapsto> A' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P
    \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t Claim (A\<heavy_comma> B) claim \<longmapsto> (A' \<heavy_comma> B) \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<and>disjoint rcssB claim"
  unfolding Cast_def by (auto simp add: Retained_def \<nu>Dependency_of_set_retained)

lemma [simp]: "Claim (Claim T claim1) claim2 = Claim T (claim2 \<union> claim1)"
  unfolding \<nu>set_eq_iff by (auto simp add: Retained_def heap_extension_union)

lemma "claim' <involve> claim \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t Claim A claim \<longmapsto> Claim (Claim A claim) claim' "
  unfolding Cast_def involve_claim_def
  by (auto simp add: Retained_def) (blast intro: heap_extension_trans heap_extension_claim_subset)+

consts "ClaimSugar" :: " 'just \<Rightarrow> 'sugar " ("[\<^bold>c\<^bold>l\<^bold>a\<^bold>i\<^bold>m _]")
  \<comment> \<open>merely a syntax sugar. We define it as a constants rather than syntax object merely for the support of the
    `jumping-to-definition` feature of the Isabelle by `Ctrl-Click`\<close>
translations "[\<^bold>c\<^bold>l\<^bold>a\<^bold>i\<^bold>m claims]" <= "CONST End_of_Contextual_Stack R <Claim> claims"

subsubsection \<open>Claim clauses\<close>

text \<open>lexical elements for claim clauses, to be adhoc-overloaded\<close>
consts "total" :: " 'a \<Rightarrow> claim_key set "
consts "write" :: " 'a \<Rightarrow> claim_key set "
consts alive :: " 'a \<Rightarrow> claim_key set "
consts all :: " 'a \<Rightarrow> 'b "

definition resource_write_address :: "nat memaddr \<Rightarrow> claim_key set"
  where "resource_write_address addr = {Write (MemAddress addr)}"
lemma [intro]: "Write (MemAddress addr) \<in> resource_write_address addr"
  unfolding resource_write_address_def by simp
lemma [simp]: "a \<in> resource_write_address addr \<longleftrightarrow> a = Write (MemAddress addr)"
  unfolding resource_write_address_def by simp

definition resource_alive_address :: "nat memaddr \<Rightarrow> claim_key set"
  where "resource_alive_address addr = {Alive (MemAddress addr) }"
lemma [intro]: "Alive (MemAddress addr) \<in> resource_alive_address addr"
  unfolding resource_alive_address_def by simp
lemma [simp]: "a \<in> resource_alive_address addr \<longleftrightarrow> a = Alive (MemAddress addr)"
  unfolding resource_alive_address_def by simp

definition resource_total_address :: "nat memaddr \<Rightarrow> claim_key set"
  where "resource_total_address addr = resource_alive_address addr \<union> resource_write_address addr"
lemma [intro]: "a \<in> resource_alive_address addr \<Longrightarrow> a \<in> resource_total_address addr"
  and [intro]: "a \<in> resource_write_address addr \<Longrightarrow> a \<in> resource_total_address addr"
  unfolding resource_total_address_def by simp+
lemma [simp]: "a \<in> resource_total_address addr \<longleftrightarrow> a \<in> resource_alive_address addr \<or> a \<in> resource_write_address addr"
  unfolding resource_total_address_def by simp

definition resource_write_address_set :: "nat memaddr set \<Rightarrow> claim_key set"
  where "resource_write_address_set addrs = (Write o MemAddress) ` addrs"
lemma [intro]: "a \<in> addr \<Longrightarrow> Write (MemAddress a) \<in> resource_write_address_set addr"
  unfolding resource_write_address_set_def by simp
lemma [simp]: "a \<in> resource_write_address_set addrs \<longleftrightarrow> a \<in> (Write o MemAddress)` addrs"
  unfolding resource_write_address_set_def by simp

definition resource_alive_address_set :: "nat memaddr set \<Rightarrow> claim_key set"
  where "resource_alive_address_set addrs = (Alive o MemAddress)` addrs"
lemma [intro]: "a \<in> addr \<Longrightarrow> Alive (MemAddress a) \<in> resource_alive_address_set addr"
  unfolding resource_alive_address_set_def by simp
lemma [simp]: "a \<in> resource_alive_address_set addrs \<longleftrightarrow> a \<in> (Alive o MemAddress)` addrs"
  unfolding resource_alive_address_set_def by simp

definition resource_total_address_set :: "nat memaddr set \<Rightarrow> claim_key set"
  where "resource_total_address_set addr = resource_alive_address_set addr \<union> resource_write_address_set addr"
lemma [intro]: "a \<in> resource_alive_address_set addr \<Longrightarrow> a \<in> resource_total_address_set addr"
  and [intro]: "a \<in> resource_write_address_set addr \<Longrightarrow> a \<in> resource_total_address_set addr"
  unfolding resource_total_address_set_def by simp+
lemma [simp]: "a \<in> resource_total_address_set addrs \<longleftrightarrow> a \<in> resource_alive_address_set addrs \<or> a \<in> resource_write_address_set addrs"
  unfolding resource_total_address_set_def by simp

adhoc_overloading "write" resource_write_address resource_write_address_set
  and alive resource_alive_address resource_alive_address_set
  and total resource_total_address resource_total_address_set

definition array :: " nat memaddr \<Rightarrow> nat \<Rightarrow> nat memaddr set "
  where "array addr n = (case addr of base |+ ofs \<Rightarrow> { (base |+ ofs') | ofs'. ofs \<le> ofs' \<and> ofs' < ofs + n})"

lemma [intro]: "i < n \<Longrightarrow> base |+ ofs + i \<in> array (base |+ ofs) n" unfolding array_def by simp
lemma [intro]: "ofs' \<le> ofs \<Longrightarrow> ofs < ofs' + n \<Longrightarrow> base |+ ofs \<in> array (base |+ ofs') n" unfolding array_def by simp
lemma [simp]: "base |+ ofs \<in> array (base' |+ ofs') n \<longleftrightarrow>  base = base' \<and> ofs' \<le> ofs \<and> ofs < ofs' + n"
  unfolding array_def by simp
lemma in_array_full_rew: "x \<in> array addr n \<longleftrightarrow>
  segment_of_addr x = segment_of_addr addr \<and> offset_of_addr addr \<le> offset_of_addr x \<and> offset_of_addr x < offset_of_addr addr + n"
  by (cases x, cases addr) simp

definition "union_of_sets l = \<Union> (set l)"
lemma [simp,disj_simp]: "union_of_sets [] = {}" and [simp,disj_simp]: "union_of_sets (h # ls) = union_of_sets ls \<union> h"
  unfolding union_of_sets_def by auto
adhoc_overloading all union_of_sets

subsubsection \<open>Disjointness\<close>

lemmas [disj_simp] = Un_empty_left Un_empty_right Un_ac Un_insert_left Un_insert_right

lemma [disj_simp]: "A \<perpendicular> B \<equiv> B \<perpendicular> A" unfolding disjoint_def by (simp add: Int_commute)
lemma [disj_intro]: "S \<perpendicular> {}" and [disj_intro]: "{} \<perpendicular> S" unfolding disjoint_def by auto
lemma [disj_intro]: "A \<perpendicular> B \<Longrightarrow> A \<perpendicular> C \<Longrightarrow>  A \<perpendicular> B \<union> C" and [disj_intro]: "A \<perpendicular> C \<Longrightarrow> B \<perpendicular> C \<Longrightarrow>  A \<union> B \<perpendicular> C"
  unfolding disjoint_def set_eq_iff by auto
lemma [disj_intro]: "x \<notin> A \<Longrightarrow> A \<perpendicular> B \<Longrightarrow>  A \<perpendicular> (insert x B)" and [disj_intro]: "x \<notin> B \<Longrightarrow> A \<perpendicular> B \<Longrightarrow> (insert x A) \<perpendicular> B"
  unfolding disjoint_def set_eq_iff by auto
lemma [disj_intro]: "x \<notin> A \<Longrightarrow> x \<notin> B \<Longrightarrow> x \<notin> A \<union> B"and [disj_intro]: "x \<noteq> y \<Longrightarrow> x \<notin> A \<Longrightarrow> x \<notin> (insert y A)" by auto

subsubsection \<open>Involvement\<close>

lemma [disj_intro]: "A <involve> A" unfolding involve_claim_def by auto
lemma [disj_intro]: "x \<in> C \<Longrightarrow> A <involve> C \<Longrightarrow> (insert x A) <involve> C"
  and [disj_intro]: "A <involve> C \<Longrightarrow> B <involve> C \<Longrightarrow> A \<union> B <involve> C"
  unfolding involve_claim_def by auto
lemma [disj_intro]: "x \<in> A \<Longrightarrow> x \<in> A \<union> B"and [disj_intro]: "x \<in> B \<Longrightarrow> x \<in> A \<union> B" and [disj_intro]: "x \<in> insert x A" by auto
lemma [disj_intro]: "x <involve> L ! i \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e i < length L \<Longrightarrow> x <involve> union_of_sets L"
  unfolding Premise_def involve_claim_def union_of_sets_def by (meson Sup_upper2 nth_mem) 

lemma [disj_intro]: "addr \<in> addrs \<Longrightarrow> (resource_write_address addr) <involve> (resource_write_address_set addrs)"
  and [disj_intro]: "addr \<in> addrs \<Longrightarrow> (resource_alive_address addr) <involve> (resource_alive_address_set addrs)"
  and [disj_intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ofs' \<le> ofs \<and> ofs < ofs' + n \<Longrightarrow> (base |+ ofs) \<in> array (base |+ ofs') n"
  unfolding involve_claim_def by auto

lemma [disj_intro]: "(resource_alive_address a) \<perpendicular> (resource_write_address b)"
  and [disj_intro]: "(resource_alive_address a) \<perpendicular> (resource_write_address_set bs)"
  and [disj_intro]: "(resource_alive_address_set as) \<perpendicular> (resource_write_address b)"
  and [disj_intro]: "(resource_alive_address_set as) \<perpendicular> (resource_write_address_set bs)"
  and [disj_intro]: "a \<notin> as \<Longrightarrow> (resource_alive_address a) \<perpendicular> (resource_alive_address_set as)"
  and [disj_intro]: "b \<notin> bs \<Longrightarrow> (resource_write_address b) \<perpendicular> (resource_write_address_set bs)"
  and [disj_intro]: "a \<noteq> a' \<Longrightarrow> (resource_alive_address a) \<perpendicular> (resource_alive_address a')"
  and [disj_intro]: "b \<noteq> b' \<Longrightarrow> (resource_write_address b) \<perpendicular> (resource_write_address b')"
  and [disj_intro]: "bs \<perpendicular> bs' \<Longrightarrow> (resource_write_address_set bs) \<perpendicular> (resource_write_address_set bs')"
  and [disj_intro]: "as \<perpendicular> as' \<Longrightarrow> (resource_alive_address_set as) \<perpendicular> (resource_alive_address_set as')"
  and [disj_intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e base \<noteq> base' \<or> ofs < ofs' \<or> ofs' + n \<le> ofs \<Longrightarrow> (base |+ ofs) \<notin> array (base' |+ ofs') n"
  unfolding disjoint_def by auto


 subsubsection \<open>Auto construct & destruct\<close>

definition AutoConstruct :: " 'exp \<Rightarrow> ('a::lrep \<longmapsto> 'b::lrep) \<Rightarrow> 'a \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> bool "("\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t _/ \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<blangle>_/ \<longmapsto> _ \<brangle>)" [20,101,10,10] 100)
  where [\<nu>def]:"AutoConstruct exp f S T \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle>"
lemma AutoConstruct: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> AutoConstruct exp f S T \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)" for exp :: "'exp"
  unfolding AutoConstruct_def using apply_proc .

(* lemma [simp]: "(Inhabited A \<and> Inhabited B) \<or> (Inhabited A' \<and> Inhabited B')
  \<Longrightarrow> (A\<heavy_comma>B) = (A'\<heavy_comma>B') \<longleftrightarrow> A = A' \<and> B = B'" unfolding Stack_Delimiter_def Inhabited_def by (auto simp add: times_eq_iff) 
lemma  [elim]: "(A\<heavy_comma>B) = (A'\<heavy_comma>B') \<Longrightarrow> (A = {} \<or> B = {} \<Longrightarrow> A' = {} \<or> B' = {} \<Longrightarrow> C) \<Longrightarrow> (A = A' \<Longrightarrow> B = B' \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Stack_Delimiter_def by (auto simp add: times_eq_iff)
*)


end
