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
datatype memaddr = memaddr (segment_of_addr: msegment) (offset_of_addr: int ) (infix "|+" 60)

lemma memaddr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>base ofs. P (base  |+ ofs))" by (metis memaddr.exhaust)
lemma memaddr_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>base ofs. P (base  |+ ofs))" by (metis memaddr.exhaust)

instantiation memaddr :: zero begin
definition zero_memaddr :: memaddr where "zero_memaddr = 0 |+ 0"
instance by standard
end

datatype deep_model = DM_int nat nat | DM_pointer nat memaddr | DM_fusion deep_model deep_model
  | DM_record deep_model | DM_array "deep_model list" | DM_none

datatype resource_key = MemAddress memaddr | ChainDB_key nat | Dispose resource_key
  \<comment> \<open>The write operation on address `addr` requires owning of resource `MemAddress addr`,
    while the dispose of that memory on `addr` requires both owning of resource `MemAddress addr`
      and `Dispose (MemAddress addr)`\<close>

type_synonym heap = "resource_key \<rightharpoonup> deep_model"

definition AvailableSegments :: "heap \<Rightarrow> msegment set"
  where "AvailableSegments heap = {seg. \<forall>ofs. heap (MemAddress (seg |+ ofs)) = None}"
definition Heap :: "heap \<Rightarrow> bool" where "Heap h \<longleftrightarrow> infinite (AvailableSegments h) \<and> MemAddress 0 \<notin> dom h"

lemma [intro]: "k \<noteq>MemAddress 0 \<Longrightarrow> Heap h \<Longrightarrow> Heap (h(k := v))" proof -
  have "AvailableSegments h \<subseteq> {(case k of MemAddress (seg |+ ofs) \<Rightarrow> seg)} \<union> (AvailableSegments (h(k := v)))"
    unfolding AvailableSegments_def by auto 
  then show "k \<noteq>MemAddress 0 \<Longrightarrow> Heap h \<Longrightarrow> Heap (h(k := v))" 
    unfolding Heap_def using infinite_super by auto
qed

definition "malloc h = (@x. h (MemAddress x) = None)"
lemma malloc: "Heap h \<Longrightarrow> h (MemAddress (malloc h)) = None"
  unfolding Heap_def AvailableSegments_def malloc_def by (rule someI_ex) (blast dest: not_finite_existsD)


text \<open>The semantic framework follows a style of shallow embedding, where semantics for different type (e.g. integers, floats)
  are modelled by different Isabelle type. Model types are constrained by the base type class {\it lrep} and types representing
  objects that supports certain features are constrained by specific sub-classes which extend the base class {\it lrep} finally. \<close>

datatype llty = llty_int nat \<comment> \<open>int bits\<close> | llty_pointer nat \<comment> \<open>pointer space\<close> | llty_tup llty | llty_array llty nat | llty_nil | llty_fusion llty llty

class lrep =  \<comment>\<open>The basic class for types modelling concrete objects\<close>
  fixes llty :: " 'a itself \<Rightarrow> llty "
  fixes deepize :: " 'a \<Rightarrow> deep_model "
  fixes shallowize :: " deep_model \<Rightarrow> 'a "
  assumes deepize_inj[simp]: " shallowize (deepize x) = x "

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
type_synonym 'a \<nu>set = " heap \<Rightarrow> 'a set "

definition NuSet :: " 'a \<nu>set \<Rightarrow> bool " where "NuSet S \<longleftrightarrow> (\<forall>h adr v p. h adr = None \<longrightarrow> p \<in> S h \<longrightarrow> p \<in> S (h(adr := v)))"


subsection \<open>The \<nu>-type\<close>

subsubsection \<open>Definitions\<close>

(* ceq : INF *)

datatype ('a,'b) typing = typing 'b "('a,'b) \<nu>" (infix "\<tycolon>" 15) \<comment>\<open>shortcut keys "<ty>"\<close>
primrec nu_of :: "('a,'b) typing \<Rightarrow> ('a,'b) \<nu>" where "nu_of (x \<tycolon> N) = N"
primrec image_of :: "('a,'b) typing \<Rightarrow> 'b" where "image_of (x \<tycolon> N) = x"

definition RepSet :: "('a,'b) typing \<Rightarrow> heap \<Rightarrow> 'a set" ("\<tort_lbrace> _ \<tort_rbrace>" [10] ) where "\<tort_lbrace> ty \<tort_rbrace> = (\<lambda>res. {p. case ty of (x \<tycolon> N) \<Rightarrow> N res p x })"
abbreviation Refining :: "heap \<Rightarrow> 'a \<Rightarrow> ('a,'b) \<nu> \<Rightarrow>  'b \<Rightarrow> bool" ("([_] _/ \<nuLinkL> _  \<nuLinkR>/ _)" [15, 27,15,27] 26) \<comment>\<open>shortcut keys "--<" and ">--"\<close>
  where  "([res] p \<nuLinkL> N \<nuLinkR> x) \<equiv> p \<in> \<tort_lbrace>x \<tycolon> N\<tort_rbrace> res"
definition Inhabited :: " (heap \<Rightarrow> 'a set) \<Rightarrow> bool" where "Inhabited s \<equiv> (\<exists>x res. x \<in> s res)"
abbreviation InhabitTyp :: " 'b \<Rightarrow> ('a::lrep,'b) \<nu> \<Rightarrow> bool" (infix "\<ratio>" 15)  \<comment>\<open>shortcut keys ":TY:"\<close>
  where  "(x \<ratio> N) \<equiv> Inhabited \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
text \<open>The @{term "x \<tycolon> N"} is a predication specifying concrete values,
  e.g. @{prop "a_concrete_int32 \<in> \<tort_lbrace>(42::nat) \<tycolon> N 32\<tort_rbrace> heap"} and also "state \<in> State (\<tort_lbrace>42 \<tycolon> N\<tort_rbrace> \<times> \<tort_lbrace>24 \<tycolon> N\<tort_rbrace> \<times> \<cdots> )".
  It constitutes basic elements in specification.
  The @{prop "[heap] p \<nuLinkL> N \<nuLinkR> x"} as the abbreviation of $p \<in> (x \<tycolon> N)$ is an abstraction between concrete value @{term p} and
  abstracted {\it image} @{term x} via the \<nu>-{\it abstractor} @{term N} which defines the abstraction relationship itself.
  The next @{prop "x \<ratio> N"} is a proposition stating @{term x} is an image of abstractor @{term N} and therefore
  the \<nu>-type @{term "x \<tycolon> N"} is inhabited. Basically it is used to derive implicated conditions of images,
  e.g. @{prop "(42 \<ratio> N 32) \<Longrightarrow> 42 < 2^32"}\<close>

lemma Refining_ex: "[res] p \<nuLinkL> R \<nuLinkR> x \<equiv> R res p x" unfolding RepSet_def by simp
(* lemma [elim!,\<nu>elim]: "Inhabited (U \<times> V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> PROP C) \<Longrightarrow> PROP C" unfolding Inhabited_def by auto *)
lemma [intro]: "x \<in> S res \<Longrightarrow> Inhabited S" unfolding Inhabited_def by auto
lemma Inhabited_E: "Inhabited S \<Longrightarrow> (\<And>x res. x \<in> S res \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

subsubsection \<open>Properties\<close>

definition \<nu>Zero :: "('a::{zero,lrep},'b) \<nu> \<Rightarrow> 'b \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Zero N x \<longleftrightarrow> (\<forall>res. [res] 0 \<nuLinkL> N \<nuLinkR> x )"
definition \<nu>Equal :: "('a::{lrep,ceq}, 'b) \<nu> \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<nu>def]: "\<nu>Equal N can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 heap.
    ceqable heap p1 p2 \<and> ([heap] p1 \<nuLinkL> N \<nuLinkR> x1) \<and> ([heap] p2 \<nuLinkL> N \<nuLinkR> x2) \<longrightarrow> can_eq x1 x2 \<and> (ceq p1 p2 = eq x1 x2))"

definition \<nu>Resources_of_set :: " 'a \<nu>set \<Rightarrow> resource_key set \<Rightarrow> bool "
  where [\<nu>def]: "\<nu>Resources_of_set S rcss \<longleftrightarrow> (\<forall>heap adr v p. adr \<notin> rcss \<longrightarrow> p \<in> S heap \<longrightarrow> p \<in> S (heap(adr := v)))"
definition \<nu>Resources :: " ('a::lrep, 'b) \<nu> \<Rightarrow> ('b \<Rightarrow> resource_key set) \<Rightarrow> bool "
  where [\<nu>def]: "\<nu>Resources T rcss \<longleftrightarrow> (\<forall>x. \<nu>Resources_of_set \<tort_lbrace> x \<tycolon> T \<tort_rbrace> (rcss x))"


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
lemma [simp]: "x \<in> Named name S heap \<longleftrightarrow> x \<in> S heap" unfolding Named_def ..
lemma [\<nu>intro]: "\<nu>Resources_of_set S rcss \<Longrightarrow> \<nu>Resources_of_set (Named name S) rcss"
  unfolding \<nu>Resources_of_set_def Named_def by simp

subsubsection \<open>Parameter tag\<close>

definition ParamTag :: " 'a \<Rightarrow> bool" ("\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m _" [1000] 26) where "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<equiv> True"
lemma ParamTag: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" for x :: "'a" unfolding ParamTag_def using TrueI .
  \<comment>\<open>A tag used to indicate a parameter should be specified during application. It retains the order of the parameters to be specified.
  For example, "@{prop "\<And>bit_width value. \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m bit_width \<Longrightarrow> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m value \<Longrightarrow> P bit_wdith value"},
    the first parameter `?bit_width` will be specified first and then the "?value".\<close>
lemma [elim!,\<nu>elim]: "\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x \<Longrightarrow> C \<Longrightarrow> C" by auto

definition ParamHOL :: " 'a \<Rightarrow> bool" where "ParamHOL x = True"
lemma ParamHOL: "Trueprop (ParamHOL x) \<equiv> \<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m x" unfolding ParamTag_def ParamHOL_def .

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
  where "Stack_Delimiter a b = (\<lambda>res. (b res \<times> a res))"
translations "R \<heavy_comma> x \<tycolon> N" == "R \<heavy_comma> \<tort_lbrace>x \<tycolon> N\<tort_rbrace>"
  "x \<tycolon> N \<heavy_comma> R" == "\<tort_lbrace>x \<tycolon> N\<tort_rbrace> \<heavy_comma> R"

lemma [simp]: "(a,b) \<in> (B \<heavy_comma> A) res \<longleftrightarrow> a \<in> A res \<and> b \<in> B res" unfolding Stack_Delimiter_def by simp
lemma [intro]: "a \<in> A res \<Longrightarrow> b \<in> B res \<Longrightarrow> (a,b) \<in> (B \<heavy_comma> A) res" by simp
lemma [elim]: "ab \<in> (B \<heavy_comma> A) res \<Longrightarrow> (\<And>a b. ab = (a,b) \<Longrightarrow> a \<in> A res \<Longrightarrow> b \<in> B res \<Longrightarrow> C) \<Longrightarrow> C" unfolding Stack_Delimiter_def by (cases ab) simp
lemma [elim!,\<nu>elim]: "Inhabited (U\<heavy_comma>V) \<Longrightarrow> (Inhabited U \<Longrightarrow> Inhabited V \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

subsubsection \<open>Tag: End_of_Contextual_Stack\<close>

definition End_of_Contextual_Stack :: " 'a \<Rightarrow> 'a " ("\<^bold>E\<^bold>N\<^bold>D") where "End_of_Contextual_Stack x = x" \<comment> \<open>A tag for printing sugar\<close>
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
  where "\<S_S> T = {s. case s of Success heap x \<Rightarrow> Heap heap \<and> x \<in> T heap | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"
definition LooseStateTy :: " ('a::lrep) \<nu>set \<Rightarrow> 'a state set" ("\<S> _" [56] 55)
  where "\<S> T = {s. case s of Success heap x \<Rightarrow> Heap heap \<and> x \<in> T heap | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma [simp]: "Success heap x \<in> \<S_S> T \<equiv> Heap heap \<and> x \<in> T heap" and [simp]: "\<not> (Fail \<in> \<S_S> T)" and [simp]: "\<not> (PartialCorrect \<in> \<S_S> T)"
  and [simp]: "Success heap x \<in> \<S> T \<equiv> Heap heap \<and> x \<in> T heap" and [simp]: "\<not> (Fail \<in> \<S> T)" and [simp]: "(PartialCorrect \<in> \<S> T)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
(* lemma [dest]: "s \<in> \<S_S> T \<Longrightarrow> Inhabited T" unfolding Inhabited_def by (cases s) auto *)
    \<comment>\<open>The inhabited property can be inferred from @{term StrictStateTy} only rather than @{term LooseStateTy}. \<close>
lemma [elim]: "s \<in> \<S_S> T \<Longrightarrow> (\<And>x h. Heap h \<Longrightarrow> s = Success h x \<Longrightarrow> x \<in> T h \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma [intro]: "Heap h \<Longrightarrow> x \<in> T h \<Longrightarrow> Success h x \<in> \<S_S> T" by simp
lemma [elim]: "s \<in> \<S> T \<Longrightarrow> (\<And>x h. Heap h \<Longrightarrow> s = Success h x \<Longrightarrow> x \<in> T h \<Longrightarrow> C) \<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma [intro]: "Heap h \<Longrightarrow> x \<in> T h \<Longrightarrow> Success h x \<in> \<S> T" and [intro]: "PartialCorrect \<in> \<S> T" by simp_all
lemma LooseStateTy_upgrade: "s \<in> \<S> T \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> \<S_S> T" by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> \<S_S> T \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> \<S_S> T) \<Longrightarrow> s \<in> \<S> T" by (cases s) auto

subsubsection \<open>\<nu>-Procedure\<close>

type_synonym ('a,'b) proc = "heap \<Rightarrow> 'a \<Rightarrow> 'b state" (infix "\<longmapsto>" 0)
definition Procedure :: "('a \<longmapsto> 'b) \<Rightarrow> ('a::lrep) \<nu>set \<Rightarrow> ('b::lrep) \<nu>set \<Rightarrow> bool" ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ \<blangle>(2 _/  \<longmapsto>  _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]:"Procedure f T U \<longleftrightarrow> (\<forall>a h. Heap h \<longrightarrow> a \<in> T h \<longrightarrow> f h a \<in> \<S> U)"
definition Map :: " 'a \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> ('a \<Rightarrow> 'b) set " where "Map A B = {f. \<forall>a h. a \<in> A h \<longrightarrow> f a \<in> B h }"
definition Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<nu>set \<Rightarrow> 'b \<nu>set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<blangle>(2 _/ \<longmapsto> _ )\<brangle>)" [101,2,2] 100)
  where [\<nu>def]: "\<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle> \<equiv> \<forall>a h. a \<in> T h \<longrightarrow> f a \<in> U h"
lemma [intro]: "(\<And>x h. x \<in> T h \<Longrightarrow> f x \<in> U h) \<Longrightarrow> \<^bold>m\<^bold>a\<^bold>p f \<blangle> T \<longmapsto> U \<brangle>" by auto
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
  CodeBlock_def: "CodeBlock stat arg ty prog \<longleftrightarrow> (Heap (fst arg) \<and> (snd arg) \<in> ty (fst arg) \<and> prog (fst arg) (snd arg) = stat \<and> stat \<noteq> PartialCorrect)"
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
  from prems(2) have sa: "Heap (fst a) \<and> snd a \<in> S (fst a) \<and> f (fst a) (snd a) = f (fst a) (snd a) \<and> f (fst a) (snd  a) \<noteq> PartialCorrect" 
    by (cases "f (fst a) (snd a)") (auto simp add: bind_def)
  note th = prems(1)[OF sa, simplified prems(2)[THEN conjunct1]]
  from th[THEN SpecTop_focus] show "s' \<in> \<S_S> T" using prems(2) by (blast intro: LooseStateTy_upgrade)
  from th[THEN SpecTop_facts] show "PROP L" .
qed done

lemma codeblock_export: "PROP Pure.prop (\<And>s. CodeBlock s a T f \<Longrightarrow> PROP C) \<Longrightarrow> PROP Pure.prop (\<And>s. CodeBlock s a T (f \<nuInstrComp> g) \<Longrightarrow> PROP C)"
  unfolding CodeBlock_def prop_def instr_comp_def proof -
  assume A[of "f (fst a) (snd a)", simplified]: "(\<And>s. Heap (fst a) \<and> snd a \<in> T (fst a) \<and> f (fst a) (snd a) = s \<and> s \<noteq> PartialCorrect \<Longrightarrow> PROP C)"
  fix s show "Heap (fst a) \<and> snd a \<in> T (fst a) \<and> bind (f (fst a) (snd a)) g = s \<and> s \<noteq> PartialCorrect \<Longrightarrow> PROP C" proof -
    assume [unfolded bind_def]: "Heap (fst a) \<and> snd a \<in> T (fst a) \<and> bind (f (fst a) (snd a)) g = s \<and> s \<noteq> PartialCorrect"
    then have "Heap (fst a) \<and> snd a \<in> T (fst a) \<and> f (fst a) (snd a) \<noteq> PartialCorrect" by auto
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
  where   "ExTyp T h = {x. (\<exists>z. x \<in> (T z h))}"
notation ExTyp (binder "\<exists>\<^sup>\<nu> " 10)

  \<comment> \<open>which represents there exists some \<nu>-images (or rarely abstractors) subject to the typing.
    And then the image subjecting the typing could be fixed as a local variable by the \<nu>-obtain command. \<close>

lemma [simp]: "x \<in> (ExTyp T) heap \<equiv> (\<exists>z. x \<in> T z heap)" unfolding ExTyp_def by auto
lemma [simp]: "(ExTyp A \<heavy_comma> R) = (\<exists>* x. (A x \<heavy_comma> R))" unfolding ExTyp_def by (rule ext) auto
lemma [simp]: "(S\<heavy_comma> ExTyp T) = (\<exists>* z. (S \<heavy_comma> T z))" unfolding ExTyp_def by (rule ext) auto
lemma ExTyp_strip: "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n (ExTyp T)) \<equiv> (\<exists>x. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t p \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T x)"
  unfolding ExTyp_def CurrentConstruction_def by (rule eq_reflection) auto


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

definition AddtionTy :: " 'a \<nu>set \<Rightarrow> bool \<Rightarrow> 'a \<nu>set " (infixl "\<addition>" 50) where " (T \<addition> P) heap = {x. x \<in> T heap \<and> P}"
lemma [simp]: "T \<addition> True = T" unfolding AddtionTy_def by fast
lemma [simp]: "x \<in> (T \<addition> P) heap \<longleftrightarrow> x \<in> T heap \<and> P" unfolding AddtionTy_def by auto
lemma [intro]: "P \<Longrightarrow> x \<in> T heap \<Longrightarrow> x \<in> (T \<addition> P) heap" unfolding AddtionTy_def by auto
lemma [elim]: "x \<in> (T \<addition> P) heap \<Longrightarrow> (x \<in> T heap \<Longrightarrow> P \<Longrightarrow> C) \<Longrightarrow> C" unfolding AddtionTy_def by auto
lemma [simp]: "(R \<heavy_comma> T \<addition> P) = ((R \<heavy_comma> T) \<addition> P)" unfolding AddtionTy_def by auto
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

  subsection \<open>Cast\<close>

definition Cast :: " 'a \<nu>set \<Rightarrow> 'a \<nu>set \<Rightarrow> bool \<Rightarrow> bool " ("(2\<^bold>c\<^bold>a\<^bold>s\<^bold>t _ \<longmapsto> _/ \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e _)" [2,2,14] 13)
  where "(\<^bold>c\<^bold>a\<^bold>s\<^bold>t A \<longmapsto> B \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P) \<longleftrightarrow> (\<forall>x heap. x \<in> A heap \<longrightarrow> x \<in> B heap \<and> P)"
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

definition disjoint (infix "\<perpendicular>" 60) where "disjoint A B \<equiv> (A \<inter> B = {})"
definition involve_claim :: " resource_key set \<Rightarrow> resource_key set \<Rightarrow> bool" (infix "<involve>" 50)
  where "involve_claim = (\<subseteq>)"

subsubsection \<open>Abstractor\<close>

definition Claim :: " ('a::lrep) \<nu>set \<Rightarrow> resource_key set \<Rightarrow> ('a::lrep) \<nu>set " (infix "<Claim>" 60)
  where "Claim S claim = (if \<nu>Resources_of_set S (- claim) then S else (\<lambda>map. {}))"

lemma [simp]: "p \<in> Claim T claim heap \<longleftrightarrow> p \<in> T heap \<and> \<nu>Resources_of_set T (- claim)" unfolding Claim_def by auto
lemma [simp]: "Claim (Claim T claim1) claim2 = Claim T (claim1 \<union> claim2)"
  unfolding Claim_def \<nu>Resources_of_set_def  by auto

lemma "\<nu>Resources_of_set B rcssB \<Longrightarrow> disjoint rcssB claim  \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t (Claim A claim \<heavy_comma> B) \<longmapsto> Claim (A\<heavy_comma> B) claim"
  unfolding Stack_Delimiter_def \<nu>Resources_of_set_def Cast_def disjoint_def by (auto simp add: \<nu>Resources_of_set_def)

lemma [\<nu>intro]:
  " claims' <involve> claims \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t (End_of_Contextual_Stack R <Claim> claims) \<longmapsto> (End_of_Contextual_Stack R <Claim> claims') "
  unfolding Cast_def involve_claim_def End_of_Contextual_Stack_def by (auto simp add: \<nu>Resources_of_set_def)

consts "ClaimSugar" :: " 'just \<Rightarrow> 'sugar " ("[\<^bold>c\<^bold>l\<^bold>a\<^bold>i\<^bold>m _]")
  \<comment> \<open>merely a syntax sugar. We define it as a constants rather than syntax object merely for the support of the
    `jumping-to-definition` feature of the Isabelle by `Ctrl-Click`\<close>
translations "[\<^bold>c\<^bold>l\<^bold>a\<^bold>i\<^bold>m claims]" <= "CONST End_of_Contextual_Stack R <Claim> claims"

subsubsection \<open>Claim clauses\<close>

text \<open>lexical elements for claim clauses, to be adhoc-overloaded\<close>
consts "write" :: " 'a \<Rightarrow> resource_key set "
consts dispose :: " 'a \<Rightarrow> resource_key set "
consts all :: " 'a \<Rightarrow> 'b "

definition resource_write_address :: "memaddr \<Rightarrow> resource_key set"
  where "resource_write_address addr = {MemAddress addr }"
lemma [simp]: "a \<in> resource_write_address addr \<longleftrightarrow> a = MemAddress addr" unfolding resource_write_address_def by simp

definition resource_dipose_address :: "memaddr \<Rightarrow> resource_key set"
  where "resource_dipose_address addr = {Dispose (MemAddress addr) }"
lemma [simp]: "a \<in> resource_dipose_address addr \<longleftrightarrow> a = Dispose (MemAddress addr)"
  unfolding resource_dipose_address_def by simp

definition resource_write_address_set :: "memaddr set \<Rightarrow> resource_key set"
  where "resource_write_address_set addrs = MemAddress` addrs"
lemma [simp]: "a \<in> resource_write_address_set addrs \<longleftrightarrow> a \<in> MemAddress` addrs"
  unfolding resource_write_address_set_def by simp

definition resource_dispose_address_set :: "memaddr set \<Rightarrow> resource_key set"
  where "resource_dispose_address_set addrs = (Dispose o MemAddress)` addrs"
lemma [simp]: "a \<in> resource_dispose_address_set addrs \<longleftrightarrow> a \<in> (Dispose o MemAddress)` addrs"
  unfolding resource_dispose_address_set_def by simp

adhoc_overloading "write" resource_write_address resource_write_address_set
  and dispose resource_dipose_address resource_dispose_address_set

definition array :: " memaddr \<Rightarrow> nat \<Rightarrow> memaddr set "
  where "array addr n = (case addr of base |+ ofs \<Rightarrow> { (base |+ ofs') | ofs'. ofs \<le> ofs' \<and> ofs' < ofs + int n})"
lemma [simp]: "base |+ ofs \<in> array (base' |+ ofs') n \<longleftrightarrow>  base = base' \<and> ofs' \<le> ofs \<and> ofs < ofs' + int n"
  unfolding array_def by simp

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
  and [disj_intro]: "addr \<in> addrs \<Longrightarrow> (resource_dipose_address addr) <involve> (resource_dispose_address_set addrs)"
  and [disj_intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e ofs' \<le> ofs \<and> ofs < ofs' + int n \<Longrightarrow> (base |+ ofs) \<in> array (base |+ ofs') n"
  unfolding involve_claim_def by auto

notepad
begin
  assume A[simplified disj_simp]: "(resource_write_address a) \<perpendicular> (resource_dispose_address_set b)"
end

lemma [disj_intro]: "(resource_dipose_address b) \<perpendicular> (resource_write_address a)"
  and [disj_intro]: "(resource_dipose_address b) \<perpendicular> (resource_write_address_set as)"
  and [disj_intro]: "(resource_dispose_address_set bs) \<perpendicular> (resource_write_address a)"
  and [disj_intro]: "(resource_dispose_address_set bs) \<perpendicular> (resource_write_address_set as)"
  and [disj_intro]: "b \<notin> bs \<Longrightarrow> (resource_dipose_address b) \<perpendicular> (resource_dispose_address_set bs)"
  and [disj_intro]: "a \<notin> as \<Longrightarrow> (resource_write_address a) \<perpendicular> (resource_write_address_set as)"
  and [disj_intro]: "b \<noteq> b' \<Longrightarrow> (resource_dipose_address b) \<perpendicular> (resource_dipose_address b')"
  and [disj_intro]: "a \<noteq> a' \<Longrightarrow> (resource_write_address a) \<perpendicular> (resource_write_address a')"
  and [disj_intro]: "as \<perpendicular> as' \<Longrightarrow> (resource_write_address_set as) \<perpendicular> (resource_write_address_set as')"
  and [disj_intro]: "bs \<perpendicular> bs' \<Longrightarrow> (resource_dispose_address_set bs) \<perpendicular> (resource_dispose_address_set bs')"
  and [disj_intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e base \<noteq> base' \<or> ofs < ofs' \<or> ofs' + int n \<le> ofs \<Longrightarrow> (base |+ ofs) \<notin> array (base' |+ ofs') n"
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
