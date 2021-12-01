(* KEEP IT SIMPLE AND STUPID *)

theory NuPrime \<comment> \<open>The Primary Theory of the \<nu>-System\<close>
  imports Main "HOL-Library.Monad_Syntax" NuHelpMath
  abbrevs "<is>" = "\<^bold>i\<^bold>s"
      and "as" = "\<^bold>a\<^bold>s"
      and "<at>" = "\<^bold>a\<^bold>t"
      and "<and>" = "\<^bold>a\<^bold>n\<^bold>d"
      and "in" = "\<^bold>i\<^bold>n"
      and "<with>" = "\<^bold>w\<^bold>i\<^bold>t\<^bold>h"
      and "<facts>" = "\<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s"
      and "<proc>" = "\<^bold>p\<^bold>r\<^bold>o\<^bold>c"
      and "<func>" = "\<^bold>f\<^bold>u\<^bold>n\<^bold>c"
      and "<map>" = "\<^bold>m\<^bold>a\<^bold>p"
      and "<param>" = "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m"
      and ",," = "\<heavy_comma>"
      and "<cast>" = "\<^bold>c\<^bold>a\<^bold>s\<^bold>t"
      and "<conversion>" = "\<^bold>c\<^bold>o\<^bold>n\<^bold>v\<^bold>e\<^bold>r\<^bold>s\<^bold>i\<^bold>o\<^bold>n"
      and "<auto>" = "\<^bold>a\<^bold>u\<^bold>t\<^bold>o"
      and "<premise>" = "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e"
      and "<construct>" = "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t"
      and "by" = "\<^bold>b\<^bold>y"
      and "<simplify>" = "\<^bold>s\<^bold>i\<^bold>m\<^bold>p\<^bold>l\<^bold>i\<^bold>f\<^bold>y"
      and "<END>" = "\<^bold>E\<^bold>N\<^bold>D"
      and "<heap>" = "\<^bold>h\<^bold>e\<^bold>a\<^bold>p"
      and "<stack>" = "\<^bold>s\<^bold>t\<^bold>a\<^bold>c\<^bold>k"
      and "<dual>" = "\<^bold>d\<^bold>u\<^bold>a\<^bold>l"
      and "<when>" = "\<^bold>w\<^bold>h\<^bold>e\<^bold>n"
      and "<intro>" = "\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o"
      and "<dest>" = "\<^bold>d\<^bold>e\<^bold>s\<^bold>t"
      and "<try>" = "\<^bold>t\<^bold>r\<^bold>y"
begin

text \<open>The fundamental theory for \<nu>-system\<close>

section Preliminary

ML_file NuConfig.ML
bundle show_more1 = [[show_hyps = true, show_types = true, show_sorts = true]]
bundle show_more = [[show_hyps = true, show_types = true]]
bundle show_hyps = [[show_hyps = true]]

named_theorems \<nu>elim "\<nu>-type elimination rules"
named_theorems \<nu>def \<open>primitive definitions used to unfold in proofs of primitive instructions.\<close>
  (* and \<nu>address_def \<open>primitive definitions for unfolding in proofs for address\<close> *)
  and \<nu>post_construct and \<nu>auto_destruct
named_theorems typing_expn "expansion theorems for abstractions" and lrep_exps and nu_exps

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

subsection \<open>Memory Pointer\<close>

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


subsection \<open>Function table & Function pointer\<close>

typedef fun_addr = "UNIV :: nat set" ..

subsection \<open>Deep Value Model\<close>

datatype deep_model = DM_int nat nat | DM_pointer "nat memaddr" | DM_fusion deep_model deep_model
  | DM_record deep_model | DM_array "deep_model list" | DM_fun_addr fun_addr | DM_none

subsection \<open>Memory & Heap\<close>

datatype resource_key = MemAddress "nat memaddr" | ChainDB_key nat
  \<comment> \<open>The write operation on address `addr` requires owning of resource `MemAddress addr`,
    while the dispose of that memory on `addr` requires both owning of resource `MemAddress addr`
      and `Dispose (MemAddress addr)`\<close>

lemma resource_key_forall: "All P \<longleftrightarrow> (\<forall>addr. P (MemAddress addr)) \<and> (\<forall>n. P (ChainDB_key n))" by (metis resource_key.exhaust)
lemma resource_key_exists: "Ex P \<longleftrightarrow> (\<exists>addr. P (MemAddress addr)) \<or> (\<exists>n. P (ChainDB_key n))" by (metis resource_key.exhaust)

type_synonym heap = "resource_key \<rightharpoonup> deep_model"

subsection \<open>State Model\<close>

datatype 'a state = Success "heap \<times> 'a" | Fail | PartialCorrect
text\<open> The basic state of the \<nu>-system virtual machine is represented by type "('a::lrep) state"}.
  The valid state `Success` essentially has two major form, one without registers and another one with them,
      \<^item> "StatOn (x1, x2, \<cdots>, xn, void)",
  where "(x1, x2, \<cdots>, xn, void)" represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term PartialCorrect} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term PartialCorrect} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>

declare state.split[split]

type_synonym ('a,'b) proc = " (heap \<times> 'a) \<Rightarrow> 'b state" (infix "\<longmapsto>" 0)

consts fun_table :: " fun_addr \<rightharpoonup> 'a \<longmapsto> 'b "
consts fun_addr_NULL :: fun_addr

specification (fun_table)
  fun_addr_NULL: "fun_table fun_addr_NULL = None" by auto





definition AvailableSegments :: "heap \<Rightarrow> msegment set"
  where "AvailableSegments heap = {seg. \<forall>ofs. heap (MemAddress (seg |+ ofs)) = None}"

definition Heap :: "heap \<Rightarrow> bool" where "Heap h \<longleftrightarrow> infinite (AvailableSegments h)"

lemma [intro]: "Heap h \<Longrightarrow> Heap (h(k := v))" proof -
  have "AvailableSegments h \<subseteq> {(case k of MemAddress (seg |+ ofs) \<Rightarrow> seg)} \<union> (AvailableSegments (h(k := v)))"
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

text \<open>The semantic framework follows a style of shallow embedding, where semantics for different type (e.g. integers, floats)
  are modelled by different Isabelle type. Model types are constrained by the base type class {\it lrep} and types representing
  objects that supports certain features are constrained by specific sub-classes which extend the base class {\it lrep} finally. \<close>

datatype llty = llty_int nat \<comment> \<open>int bits\<close> | llty_pointer | llty_tup llty | llty_array llty nat | llty_nil | llty_fusion llty llty | Lty_fun_addr

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


subsection \<open>The \<nu>-type\<close>

type_synonym ('a,'b) \<nu> = " 'b \<Rightarrow> 'a set "

subsubsection \<open>Definitions\<close>

(* ceq : INF *)

datatype ('a,'b) typing = typing (typing_img: 'b ) (typing_nu: "('a,'b) \<nu>") ("_ \<tycolon> _" [18,18] 17) \<comment>\<open>shortcut keys "<ty>"\<close>
primrec nu_of :: "('a,'b) typing \<Rightarrow> ('a,'b) \<nu>" where "nu_of (x \<tycolon> N) = N"
primrec image_of :: "('a,'b) typing \<Rightarrow> 'b" where "image_of (x \<tycolon> N) = x"

definition RepSet :: "('a,'b) typing \<Rightarrow> 'a set" ("\<tort_lbrace> _ \<tort_rbrace>" [10] ) where "\<tort_lbrace> ty \<tort_rbrace> = (case ty of (x \<tycolon> N) \<Rightarrow> N x)"
definition Refining :: "'a \<Rightarrow> ('a,'b) \<nu> \<Rightarrow>  'b \<Rightarrow> bool" ("(_/ \<nuLinkL> _  \<nuLinkR>/ _)" [27,15,27] 26) \<comment>\<open>shortcut keys "--<" and ">--"\<close>
  where  "(p \<nuLinkL> N \<nuLinkR> x) \<longleftrightarrow> p \<in> N x"
definition Inhabited :: " 'a set \<Rightarrow> bool" where  "Inhabited S = (\<exists>p. p \<in> S)"
abbreviation InhabitNu :: " 'b \<Rightarrow> ('a,'b) \<nu> \<Rightarrow> bool" ("_ \<ratio> _" [18,18] 17)  \<comment>\<open>shortcut keys ":TY:"\<close>
  where  " (x \<ratio> T) \<equiv> Inhabited \<tort_lbrace>x \<tycolon> T\<tort_rbrace>"
text \<open>The @{term "x \<tycolon> N"} is a predication specifying concrete values,
  e.g. @{prop " a_concrete_int32 \<in> \<tort_lbrace>(42::nat) \<tycolon> N 32\<tort_rbrace>"} and also "state \<in> State (\<tort_lbrace>42 \<tycolon> N\<tort_rbrace> \<times> \<tort_lbrace>24 \<tycolon> N\<tort_rbrace> \<times> \<cdots> )".
  It constitutes basic elements in specification.
  The @{prop "p \<nuLinkL> N \<nuLinkR> x"} as the abbreviation of $p \<in> (x \<tycolon> N)$ is an abstraction between concrete value @{term p} and
  abstracted {\it image} @{term x} via the \<nu>-{\it abstractor} @{term N} which defines the abstraction relationship itself.
  The next @{prop " x \<ratio> N"} is a proposition stating @{term x} is an image of abstractor @{term N} and therefore
  the \<nu>-type @{term "x \<tycolon> N"} is inhabited. Basically it is used to derive implicated conditions of images,
  e.g. @{prop "( 42 \<ratio> N 32) \<Longrightarrow> 42 < 2^32"}\<close>

lemma [simp]: "p \<in> \<tort_lbrace>x \<tycolon> T\<tort_rbrace> \<longleftrightarrow> p \<nuLinkL> T \<nuLinkR> x" unfolding RepSet_def Refining_def by simp
lemma typing_inhabited: "p \<nuLinkL> T \<nuLinkR> x \<Longrightarrow> x \<ratio> T" unfolding Refining_def Inhabited_def RepSet_def by simp blast

(* lemma [elim!,\<nu>elim]: "Inhabited (U \<times> V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> PROP C) \<Longrightarrow> PROP C" unfolding Inhabited_def by auto *)
(* lemma [intro]: "x \<in> S \<Longrightarrow> Inhabited S" unfolding Inhabited_def by auto 
lemma Inhabited_E: "Inhabited S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto *)


subsubsection \<open>Properties\<close>

definition \<nu>Zero :: "('a::{zero,lrep},'b) \<nu> \<Rightarrow> 'b \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Zero N x \<longleftrightarrow> (0 \<nuLinkL> N \<nuLinkR> x )"
definition \<nu>Equal :: "('a::{lrep,ceq}, 'b) \<nu> \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Equal N can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 heap.
    can_eq x1 x2 \<and> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> N \<nuLinkR> x2) \<longrightarrow> ceqable heap p1 p2 \<and> (ceq p1 p2 = eq x1 x2))"


  section\<open>Structures for construction\<close>

subsection \<open>Auxiliary tags\<close>

subsubsection \<open>Label tag\<close>

datatype label = LABEL_TAG "unit \<Rightarrow> unit"

lemma [cong]: "LABEL_TAG x \<equiv> LABEL_TAG x"  using reflexive .
lemma label_eq: "x = y" for x :: label by (cases x, cases y) auto

syntax "_LABEL_" :: "idt \<Rightarrow> label" ("LABEL _" [0] 1000)
translations "LABEL name" == "CONST LABEL_TAG (\<lambda>name. ())"

subsubsection \<open>Name tag by type\<close>

datatype ('x, 'name) named (infix "named" 30) = tag 'x

text \<open>It is another name tag which tags names in type by free variables, e.g., \<^typ>\<open>(nat \<times> int) named ('name_i \<times> 'name_j)\<close>.
  It is useful for the rewrite and expansion of quantification which retains name information of bound variables,
    e.g. the transformation from \<^prop>\<open>\<forall>(x::(nat \<times> int) named ('i \<times> 'j)). P x\<close> to \<^prop>\<open>\<forall>(i::nat) (j::int). P (tag (i,j))\<close>\<close>

lemma named_forall: "All P \<longleftrightarrow> (\<forall>x. P (tag x))" by (metis named.exhaust)
lemma named_exists: "Ex P \<longleftrightarrow> (\<exists>x. P (tag x))" by (metis named.exhaust)
lemma [simp]: "tag (case x of tag x \<Rightarrow> x) = x" by (cases x) simp
lemma named_All: "(\<And>x. PROP P x) \<equiv> (\<And>x. PROP P (tag x))"
proof fix x assume "(\<And>x. PROP P x)" then show "PROP P (tag x)" .
next fix x :: "'a named 'b" assume "(\<And>x. PROP P (tag x))" from \<open>PROP P (tag (case x of tag x \<Rightarrow> x))\<close> show "PROP P x" by simp
qed


subsubsection \<open>Parameter tag\<close>

definition ParamTag :: " 'a \<Rightarrow> bool" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 26) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> True"
lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
  \<comment>\<open>A tag used to indicate a parameter should be specified during application. It retains the order of the parameters to be specified.
  For example, "@{prop "\<And>bit_width value. \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_width \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> P bit_wdith value"},
    the first parameter `?bit_width` will be specified first and then the "?value".\<close>
lemma [elim!,\<nu>elim]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" by auto

subsubsection \<open>Premise tag\<close>

definition Premise :: "bool \<Rightarrow> bool" ("\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e _" [27] 26) where [\<nu>def]:"Premise x = x"
  \<comment> \<open>The tag represent a necessary premise that must be solved in a rule or procedure.
    The automatic reasoning ties to solve it, and if fails, terminates the automatic reasoning.\<close>

lemma Premise_I[intro!]: "P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P" unfolding Premise_def by simp
lemma Premise_E: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> P" unfolding Premise_def by simp

lemma [elim!,\<nu>elim]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> C" unfolding Premise_def by simp
lemma Premise_Irew: "(P \<Longrightarrow> C) \<equiv> Trueprop (\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<longrightarrow> C)" unfolding Premise_def atomize_imp .

(* attribute_setup intro_premise = \<open>
  Scan.succeed (Thm.rule_attribute [] (fn _ => fn th => th COMP @{thm Premise_I}))
\<close>*)
attribute_setup elim_premise = \<open>
  Scan.succeed (Thm.rule_attribute [] (fn _ => fn th => th COMP @{thm Premise_E}))
\<close>

subsubsection \<open>Intro and Dest tag\<close>

definition Intro :: " bool \<Rightarrow> bool " ("\<^bold>i\<^bold>n\<^bold>t\<^bold>r\<^bold>o _" [12] 11) where "Intro P = P"
definition Dest :: " bool \<Rightarrow> bool " ("\<^bold>d\<^bold>e\<^bold>s\<^bold>t _" [12] 11) where "Dest P = P"

lemma Intro_D: "Intro P \<Longrightarrow> P" unfolding Intro_def .
lemma Dest_D: "Dest P \<Longrightarrow> P" unfolding Dest_def .

subsubsection \<open>Different tag\<close>

definition Different :: " 'a \<Rightarrow> 'b \<Rightarrow> bool " where "Different A B = True"
  \<comment> \<open>A premise that solved by automatic reasoning only if the term expressions of A and B
  are not alpha-equivalent. It is useful to break up the self-loop. For example,
  while the introduction rule `cast A \<longmapsto> B \<Longrightarrow> cast B \<longmapsto> C \<Longrightarrow> cast A \<longmapsto> C` causes loop if given `cast A \<longmapsto> A`,
  the rule `cast A \<longmapsto> B \<Longrightarrow> Different A B \<Longrightarrow> cast B \<longmapsto> C \<Longrightarrow> cast A \<longmapsto> C` will not.\<close>
lemma Different_I: "Different A B" unfolding Different_def ..

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


(* subsubsection \<open>Tag: End_of_Contextual_Stack\<close>

definition End_of_Contextual_Stack :: " 'a \<Rightarrow> 'a " ("\<^bold>E\<^bold>N\<^bold>D") where [\<nu>def]: "End_of_Contextual_Stack x = x" \<comment> \<open>A tag for printing sugar\<close>
lemmas End_of_Contextual_Stack_rew = End_of_Contextual_Stack_def[THEN eq_reflection]
lemma [elim,\<nu>elim]: "Inhabited (End_of_Contextual_Stack S) \<Longrightarrow> C \<Longrightarrow> C" . *)

subsection \<open>The \<nu>-system VM and Procedure construction structures\<close>

subsubsection \<open>Types specifying states\<close>

definition StrictStateTy :: " (heap \<times> 'a::lrep) set \<Rightarrow> 'a state set" ("\<S_S> _" [56] 55)
  where "\<S_S> T = {s. case s of Success x \<Rightarrow> x \<in> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"
definition LooseStateTy :: " (heap \<times> 'a::lrep) set \<Rightarrow> 'a state set" ("\<S> _" [56] 55)
  where "\<S> T = {s. case s of Success x \<Rightarrow> x \<in> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma [iff]: "Success x \<in> \<S_S> T \<equiv> x \<in> T" and [iff]: "\<not> (Fail \<in> \<S_S> T)" and [iff]: "\<not> (PartialCorrect \<in> \<S_S> T)"
  and [iff]: "Success x \<in> \<S> T \<equiv> x \<in> T" and [iff]: "\<not> (Fail \<in> \<S> T)" and [iff]: "(PartialCorrect \<in> \<S> T)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
(* lemma [dest]: "s \<in> \<S_S> T \<Longrightarrow> Inhabited T" unfolding Inhabited_def by (cases s) auto *)
    \<comment>\<open>The inhabited property can be inferred from @{term StrictStateTy} only rather than @{term LooseStateTy}. \<close>
lemma StrictStateTy_elim[elim]: "s \<in> \<S_S> T \<Longrightarrow> (\<And>x. s = Success x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma StrictStateTy_intro[intro]: " x \<in> T \<Longrightarrow> Success x \<in> \<S_S> T" by simp
lemma LooseStateTy_E[elim]:
  "s \<in> \<S> T \<Longrightarrow> (\<And>x. s = Success x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma LooseStateTy_I[intro]:
  " x \<in> T \<Longrightarrow> Success x \<in> \<S> T" and [intro]: "PartialCorrect \<in> \<S> T" by simp_all
lemma LooseStateTy_upgrade: "s \<in> \<S> T \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> \<S_S> T" by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> \<S_S> T \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> \<S_S> T) \<Longrightarrow> s \<in> \<S> T" by (cases s) auto

subsubsection \<open>Last Heap, a modifier for frama rule\<close>

definition disjoint :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " (infixl "\<perpendicular>" 60) where "disjoint A B \<longleftrightarrow> (A \<inter> B = {})"
lemma disjoint_rewL: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<notin> B)" unfolding disjoint_def by auto
lemma disjoint_rewR: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> B \<longrightarrow> x \<notin> A)" unfolding disjoint_def by auto
lemma [elim]: "A \<perpendicular> B \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False) \<Longrightarrow> C) \<Longrightarrow> C" unfolding disjoint_def by auto

lemma [iff]: "{} \<perpendicular> S" and [iff]: "S \<perpendicular> {}" unfolding disjoint_def by auto


definition Heap_Tail :: "heap set \<Rightarrow> (heap \<times> 'a::lrep) set \<Rightarrow> (heap \<times> 'a::lrep) set" ( "_/ ^\<heavy_asterisk> _" [13,14] 13)
  where "(H ^\<heavy_asterisk> Ctx) = {(h,s). Heap h \<and> (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> h1 \<in> H \<and> (h2,s) \<in> Ctx) }"

lemma Heap_Tail_E[elim]:
  "(h,s) \<in> (H ^\<heavy_asterisk> Ctx) \<Longrightarrow> (\<And>h1 h2. h = h1 ++ h2 \<Longrightarrow> Heap (h1 ++ h2) \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> h1 \<in> H \<Longrightarrow> (h2,s) \<in> Ctx \<Longrightarrow> C) \<Longrightarrow> C "
  unfolding Heap_Tail_def by simp blast

lemma Heap_Tail_I[intro]:
  "h1 \<in> H \<Longrightarrow> (h2,s) \<in> Ctx \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> Heap (h1 ++ h2) \<Longrightarrow> (h1 ++ h2, s) \<in> (H ^\<heavy_asterisk> Ctx)"
  unfolding Heap_Tail_def by simp blast


subsubsection \<open>\<nu>-Procedure\<close>

definition Procedure :: "('a \<longmapsto> 'b) \<Rightarrow> (heap \<times> 'a::lrep) set \<Rightarrow> (heap \<times> 'b::lrep) set \<Rightarrow> bool" ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ \<blangle>(2 _/  \<longmapsto>  _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]:"Procedure f T U \<longleftrightarrow> (\<forall>a H. a \<in> (H ^\<heavy_asterisk> T) \<longrightarrow> f a \<in> \<S> (H ^\<heavy_asterisk> U))"

translations "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> a \<tycolon> A \<longmapsto> B \<brangle>" \<rightleftharpoons> "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> \<tort_lbrace> a \<tycolon> A \<tort_rbrace> \<longmapsto> B \<brangle>"
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> b \<tycolon> B \<brangle>" \<rightleftharpoons> "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> \<tort_lbrace> b \<tycolon> B \<tort_rbrace> \<brangle>"

definition Map :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set " where "Map A B = {f. \<forall>a. a \<in> A \<longrightarrow> f a \<in> B }"
definition Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<blangle>(2 _/ \<longmapsto> _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle> \<equiv> \<forall>a. a \<in> T \<longrightarrow> f a \<in> U"
(* lemma [intro]: "(\<And>x h. x \<in> T h \<Longrightarrow> f x \<in> U h) \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle>" by auto *)
(* lemma [simp]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> \<S> U \<brangle> \<longleftrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> T \<longmapsto> U \<brangle>" unfolding \<nu>def by fast  *)

definition Function ("(2\<^bold>f\<^bold>u\<^bold>n\<^bold>c _/ \<blangle>(2 _/  \<longmapsto>  _ )\<brangle>)" [101,2,2] 100) where "Function = Procedure"
translations "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> a \<tycolon> A \<longmapsto> B \<brangle>" \<rightleftharpoons> "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> \<tort_lbrace> a \<tycolon> A \<tort_rbrace> \<longmapsto> B \<brangle>"
  "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> A \<longmapsto> b \<tycolon> B \<brangle>" \<rightleftharpoons> "\<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> A \<longmapsto> \<tort_lbrace> b \<tycolon> B \<tort_rbrace> \<brangle>"

lemma Function_I: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>f\<^bold>u\<^bold>n\<^bold>c f \<blangle> A \<longmapsto> B \<brangle>" unfolding Function_def .

text \<open>One thing is, a \<^const>\<open>Procedure\<close> does not mean a low-level function in the target object,
  note the stack remainder, but only a logical procedure.
  It is not necessarily complied to a low level function (an LLVM function),
  but most of the time the call of it is inline-expanded.
  Logically the presence of stack remainder prevents it to be regarded as a standalone function,
  especially when representing function pointers and closures the remainder is cumbersome.
  For this, \<^const>\<open>Function\<close> explicitly representing a standalone function is introduced
  based on procedures whose stack remainder is always `void`
    (but the heap remainder is retained because it accords the logic),
  i.e. `func f \<blangle> void \<tycolon> Void\<heavy_comma> arg1 \<tycolon> Arg1\<heavy_comma> \<cdots> \<heavy_comma> <heap> heap_remainder \<tycolon> H\<heavy_comma> \<cdots>
    \<longmapsto> void \<tycolon> Void\<heavy_comma> ret1 \<tycolon> Ret1\<heavy_comma> \<cdots>\<heavy_comma> <heap> heap_remainder \<tycolon> H\<heavy_comma> \<cdots> \<brangle>`.
  The distinctions between Procedure and Function are, while both of them can be called and used directly in the
  interactive programming (the difference is transparent when calling then),
  \<^item> the stack remainder of a function is always void,
  \<^item> only a function can have function pointers and closures relating it,
  \<^item> only functions whose type is decided (without polymorphic variables)
    can generate low-level functions in the target object (e.g. an obj file, or a DLL file).
  \<^item> about internal implementation, the calling of a function is by a specific `op_call` instruction stating types of
    arguments and return values, so it requires slightly more time and space to reason and represent the program.\<close>


subsection \<open>Primitive operations and instructions required in the system\<close>

subsubsection \<open>Elementary instructions\<close>

definition bind :: " ('a::lrep) state \<Rightarrow> ( 'a \<longmapsto> 'b) \<Rightarrow> ('b::lrep) state " \<comment>\<open>monadic bind\<close>
  where "bind s f = (case s of Success x \<Rightarrow> f x | Fail \<Rightarrow> Fail | PartialCorrect \<Rightarrow> PartialCorrect)"
definition instr_comp :: "(('a::lrep) \<longmapsto> ('b::lrep)) \<Rightarrow> ( 'b \<longmapsto> ('c::lrep)) \<Rightarrow> 'a \<longmapsto> 'c"  ("_ \<nuInstrComp>/ _" [75,76] 75) 
  where "instr_comp f g s = bind (f s) g"
definition nop :: " ('a::lrep) \<longmapsto> 'a" where "nop = Success" \<comment>\<open>the instruction `no-operation`\<close>

lemma nop_\<nu>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<blangle> T \<longmapsto> T \<brangle>" unfolding nop_def Procedure_def by auto
lemma instr_comp[intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> A \<longmapsto> B \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> B \<longmapsto> C \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<nuInstrComp> g) \<blangle> A \<longmapsto> C \<brangle>"
  unfolding instr_comp_def Procedure_def bind_def by (auto 0 4)


subsection \<open>Top-level Construction Structures\<close>

subsubsection \<open>Construction Context & Code block\<close>

definition CurrentConstruction :: " ('a::lrep) state \<Rightarrow> heap set \<Rightarrow> (heap \<times> 'a) set \<Rightarrow> bool " ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _  [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,11] 10)
  where "CurrentConstruction s Heap_Remainder S \<longleftrightarrow> s \<in> \<S_S> (Heap_Remainder ^\<heavy_asterisk> S)"
definition PendingConstruction :: " (('a::lrep) \<longmapsto> ('b::lrep)) \<Rightarrow> 'a state \<Rightarrow> heap set \<Rightarrow> (heap \<times> 'b) set \<Rightarrow> bool "
    ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _  [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,1000,5] 4)
  where "PendingConstruction f s Heap_Remainder S \<longleftrightarrow> bind s f \<in> \<S> (Heap_Remainder ^\<heavy_asterisk> S)"
translations "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (x \<tycolon> T)" \<rightleftharpoons> "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n \<tort_lbrace> x \<tycolon> T \<tort_rbrace>"
  "CONST PendingConstruction f s H (x \<tycolon> T)" \<rightleftharpoons> "CONST PendingConstruction f s H \<tort_lbrace> x \<tycolon> T\<tort_rbrace>"

lemma CurrentConstruction_D: "CurrentConstruction s H T \<Longrightarrow> Inhabited T"
  unfolding CurrentConstruction_def Inhabited_def by (cases s) (auto 0 3)
(* lemma [elim!,\<nu>elim]: "CurrentConstruction s S \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding CurrentConstruction_def by (cases s) auto *)

definition CodeBlock :: " ('a::lrep) state \<Rightarrow> ('b::lrep) state => ('b \<longmapsto> 'a) \<Rightarrow> bool" where
  CodeBlock_def: "CodeBlock stat arg prog \<longleftrightarrow> (bind arg prog = stat \<and> stat \<noteq> PartialCorrect)"
syntax "_codeblock_exp_" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> bool"  ("(2\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _/  \<^bold>a\<^bold>s '\<open>_'\<close>/ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>)" [100,0,0] 3)
syntax "_codeblock_" :: "idt \<Rightarrow> logic \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>" [100,0] 3)

(* definition CodeBlock' :: " ('a::lrep) state \<Rightarrow> ('b::lrep) state => ('b \<longmapsto> 'a) \<Rightarrow> bool" where
  CodeBlock'_def: "CodeBlock' stat arg prog \<longleftrightarrow> (bind arg prog = stat \<and> stat \<noteq> PartialCorrect)"

lemma accept_proc'': "\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> (\<And>s'. CodeBlock' s' s g \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)" *)
  

attribute_setup show_codeblock_expression =  \<open>
  Scan.lift (Parse.$$$ "=" |-- ((Args.$$$ "false" >> K false) || (Args.$$$ "true" >> K true)) >>
    (Thm.declaration_attribute o K o Config.put_generic NuConfig.show_codeblock_expression))\<close>
(* print_translation \<open>
  let
    fun codeblock_print ctx [v,arg,ty,exp] =
      if Config.get ctx NuConfig.show_codeblock_expression
      then  Syntax.const \<^syntax_const>\<open>_codeblock_exp_\<close> $ v $ ty $ exp
      else Syntax.const \<^syntax_const>\<open>_codeblock_\<close> $ v $ ty
  in
   [(\<^const_syntax>\<open>CodeBlock\<close>, codeblock_print)]
  end
\<close>*)

(* lemma CodeBlock_unabbrev: "CodeBlock v arg ty prog \<Longrightarrow> (v \<equiv> ProtectorI (prog arg))"
  unfolding CodeBlock_def ProtectorI_def by (rule eq_reflection) fast
lemma CodeBlock_abbrev: "CodeBlock v arg ty prog \<Longrightarrow> ProtectorI (prog arg) \<equiv> v"
  unfolding CodeBlock_def ProtectorI_def by (rule eq_reflection) fast *)

subsubsection \<open>Contextual Fact\<close>

definition Fact :: "label \<Rightarrow> bool \<Rightarrow> prop" where "Fact label P \<equiv>Trueprop P"
syntax "Fact_sugar_" :: "idt \<Rightarrow> logic \<Rightarrow> prop" ("\<^item> _ : _" [5,0] 4)
translations "Fact_sugar_ name P" == "CONST Fact (LABEL name) P"
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

theorem apply_proc: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> S \<longmapsto> T \<brangle> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding Procedure_def CurrentConstruction_def PendingConstruction_def bind_def SpecTop_imp by (auto 0 5)

theorem accept_proc: "\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> CodeBlock s' s f \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  for s' :: "('b::stack) state"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def
  by (simp add: LooseStateTy_upgrade)

theorem reassemble_proc_0:
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g nop \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def nop_def bind_def by (cases s) simp+

theorem reassemble_proc:
  "(\<And>s'. CodeBlock s' s f \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s' [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<nuInstrComp> g) \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def bind_def instr_comp_def
  by force

theorem reassemble_proc_final:
  "(\<And>s H. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<blangle> S \<longmapsto> T \<brangle>"
  unfolding CurrentConstruction_def PendingConstruction_def Procedure_def bind_def pair_All
  by (metis StrictStateTy_intro state.simps(8))

(* theorem start_block:
  "((PROP X) \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L) \<Longrightarrow>
      CodeBlock s a U nop \<Longrightarrow>
      (\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n U \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP L)"
  for U :: " (heap \<times> 'a::lrep) set" and V :: "(heap \<times> 'b::lrep) set" and s :: " 'a state" and a :: "heap \<times> 'a"
  unfolding nop_def CodeBlock_def CurrentConstruction_def SpecTop_imp by (rule SpecTop_I) auto *)

lemma rename_proc: "f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<blangle> U \<longmapsto> \<R> \<brangle> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<blangle> U \<longmapsto> \<R> \<brangle>" by fast

lemma name_star_fact:   
  "(PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (Trueprop Q) (PROP L) (PROP S))
    \<Longrightarrow> (PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP NoFact) (PROP Fact name Q and_fact PROP L) (PROP S))"
  unfolding SpecTop_imp FactCollection_imp by (intro SpecTop_I FactCollection_I TrueI Fact_I AndFact_I NoFact)
lemma declare_fact:
  "A \<Longrightarrow> (PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP L) (PROP S))
    \<Longrightarrow> (PROP P \<^bold>w\<^bold>i\<^bold>t\<^bold>h \<^bold>f\<^bold>a\<^bold>c\<^bold>t\<^bold>s: PROP FactCollection (PROP Q) (PROP Fact name A and_fact PROP L) (PROP S))"
  unfolding SpecTop_imp FactCollection_imp by (intro SpecTop_I FactCollection_I TrueI Fact_I AndFact_I NoFact)


  section \<open>Supplementary structures and mechanisms for elementary functions\<close>

definition "SchemaTag x = x"

end
