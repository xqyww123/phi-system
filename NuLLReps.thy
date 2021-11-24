theory NuLLReps
  imports NuSys "HOL-Library.Word"
  abbrevs "<own>" = "\<left_fish_tail>"
    and "<none>" = "\<down_fish_tail>"
    and "<object>" = "\<R_arr_tail>"
    and "<pointer>"  = "\<TeardropAsterisk>"
begin   

text \<open>Semantic data representations\<close>

declare pair_forall[lrep_exps] pair_exists[lrep_exps]


section \<open>Memory address\<close>

text \<open>The concept of the address space is one of the notions in the LLVM\<close>

consts segment_len :: "msegment \<Rightarrow> nat" \<comment> \<open>in unit of the number of elements\<close>
consts segment_llty :: "msegment \<Rightarrow> llty" \<comment> \<open>type of the element in the segment\<close>
consts size_of :: "llty \<Rightarrow> nat" \<comment> \<open>in unit of bytes\<close>
abbreviation "address_llty adr \<equiv> segment_llty (segment_of adr)"
abbreviation "address_len adr \<equiv> segment_len (segment_of adr)"
consts addrspace_capacity :: "nat" \<comment> \<open>in unit of bits\<close>
specification (addrspace_capacity) addrspace_capacity_L0: "0 < addrspace_capacity" by auto
specification (size_of)
  size_of_L0[simp]: "size_of x \<noteq> 0"
  by auto

specification (segment_len)
  segment_len_valid: "segment_len seg * size_of (segment_llty seg) < 2 ^ (addrspace_capacity - 1)"
proof show "\<forall>seg. (\<lambda>_.  0) seg * size_of (segment_llty seg) < 2 ^ (addrspace_capacity - 1)"
    using addrspace_capacity_L0 by auto qed

lemma segment_len_valid2: "segment_len seg * size_of (segment_llty seg) < 2 ^ addrspace_capacity"
  using segment_len_valid
  by (metis addrspace_capacity_L0 le_less_trans one_less_numeral_iff order_less_imp_le power_commutes
      power_less_power_Suc power_minus_mult semiring_norm(76))

typedef size_t = "UNIV :: nat set" ..
instantiation size_t :: len begin
definition len_of_size_t :: "size_t itself \<Rightarrow> nat" where [simp]: "len_of_size_t _ = addrspace_capacity"
instance apply standard using addrspace_capacity_L0 by auto
end

definition "malloc h = (@x. \<forall>ofs. h (MemAddress (x |+ ofs)) = None)"

lemma malloc: "Heap h \<Longrightarrow> h (MemAddress (malloc h |+ ofs)) = None"
  unfolding Heap_def AvailableSegments_def malloc_def
  by (metis (mono_tags, lifting) not_finite_existsD tfl_some) 

lemma malloc2: "Heap h \<Longrightarrow> MemAddress (malloc h |+ ofs) \<notin> dom h"
  using malloc by (simp add: domIff) 


type_synonym raw_memaddr = "size_t  word memaddr"

datatype memptr = memptr "raw_memaddr "  \<comment> \<open>'spc : address space\<close>



(* specification (segment_len) segment_len_max: "segment_len seg < (2::nat) ^ addrspace_capacity (segment_space seg)"
  proof show "\<forall>seg. (\<lambda>x. 0) seg < (2::nat) ^ addrspace_capacity (segment_space seg)" by auto qed *)
(* specification (segment_len) segment_len_max: "segment_len seg * size_of (segment_llty seg) < addrspace_capacity (segment_space seg)"
  proof show "\<forall>seg. (\<lambda>x. 0) seg * size_of (segment_llty seg) < addrspace_capacity (segment_space seg)" by auto qed *)

(* typedef ('b::len0) size_t = "UNIV :: nat set" ..
instantiation size_t :: (len0) len begin
definition len_of_size_t :: "'a size_t itself \<Rightarrow> nat" where [simp]: "len_of_size_t _ = 1 + addrspace_capacity LENGTH('a)"
  \<comment> \<open>it is plus 1 to enable the representation of `negative` offset of the address exorcising any ambiguity.
    In the complication implementation, it is interpreted as this that the size of a single segment can only be at most to half of the
    actual total capacity of the address space, 2^31 bytes in the 32 bits machine, so that the size_t in this case still equals
    to that in the actual physical machine. \<close>
instance by standard auto
end *)

lemma memptr_exisits[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>addr. P (memptr addr))" by (metis memptr.exhaust) 
lemma memptr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>addr. P (memptr addr))" by (metis memptr.exhaust) 
lemma [simp]: "memptr (case x of memptr a \<Rightarrow> a) = x" by (cases x) simp
lemma memptr_All: "(\<And>x. PROP P x) \<equiv> (\<And>addr. PROP P (memptr addr))"
proof fix addr assume "\<And>x. PROP P x" then show "PROP P (memptr addr)" .
next fix x assume "\<And>addr. PROP P (memptr addr)" from \<open>PROP P (memptr (case x of memptr a \<Rightarrow> a))\<close> show "PROP P x" by simp
qed

subsection \<open>Instantiations for memptr\<close>

instantiation memptr :: lrep begin
definition llty_memptr :: " memptr itself \<Rightarrow> llty" where "llty_memptr _ = llty_pointer"
definition deepize_memptr :: " memptr \<Rightarrow> deep_model"
  where "deepize_memptr ptr = DM_pointer (case_memptr (map_memaddr unat) ptr)"
definition shallowize_memptr :: " deep_model \<Rightarrow> memptr "
  where "shallowize_memptr dm = (case dm of DM_pointer addr \<Rightarrow> memptr (map_memaddr of_nat addr))"
instance apply standard subgoal for x apply (cases x) subgoal for xa apply (cases xa)
      by (auto simp add: shallowize_memptr_def deepize_memptr_def) done done 
end

instantiation memptr :: field begin instance by standard end
instantiation memptr :: field_list begin instance by standard end

instantiation memptr :: zero begin
definition zero_memptr :: " memptr" where [simp]: "zero_memptr = memptr undefined"
instance by standard
end


abbreviation valid_memaddr :: "nat memaddr \<Rightarrow> bool"
  where "valid_memaddr addr \<equiv> offset_of addr \<le> segment_len (segment_of addr)"
definition raw_offset_of :: " msegment \<Rightarrow> nat \<Rightarrow> size_t word"
  where "raw_offset_of seg i = of_nat (i * size_of (segment_llty seg))"
lemma [simp]: "raw_offset_of seg 0 = 0" unfolding raw_offset_of_def by auto
lemma [simp]: "raw_offset_of seg (ofs + unat delt) = raw_offset_of seg ofs + delt * word_of_nat (size_of (segment_llty seg))"
  unfolding raw_offset_of_def using distrib_right by auto
lemma raw_offset_of_inj:
  "valid_memaddr (seg |+ ofs1) \<Longrightarrow> valid_memaddr (seg |+ ofs2) \<Longrightarrow>
    raw_offset_of seg ofs1 = (raw_offset_of seg ofs2 :: size_t word) \<Longrightarrow> ofs1 = ofs2"
  unfolding raw_offset_of_def word_of_nat_eq_iff take_bit_nat_def apply simp subgoal premises prems proof -
    have "ofs1 * size_of (segment_llty seg) < 2 ^ addrspace_capacity"
      using prems segment_len_valid2 size_of_L0
      by (meson le_less_trans mult_le_mono1)
    moreover have "ofs2 * size_of (segment_llty seg) < 2 ^ addrspace_capacity"
      using prems segment_len_valid2 size_of_L0
      by (meson le_less_trans mult_le_mono1) 
    ultimately show "ofs1 = ofs2" using prems size_of_L0 addrspace_capacity_L0 by auto
  qed done

definition same_addr_offset :: "msegment \<Rightarrow> size_t word \<Rightarrow> nat \<Rightarrow> bool"
  where "same_addr_offset seg ofsp ofsx \<longleftrightarrow> ofsx \<le> segment_len seg \<and> raw_offset_of seg ofsx = ofsp"
definition the_same_addr :: "raw_memaddr \<Rightarrow> nat memaddr \<Rightarrow> bool"
  where "the_same_addr addrp addrx \<equiv>
    segment_of addrp = segment_of addrx
    \<and> same_addr_offset (segment_of addrx)  (offset_of addrp) (offset_of addrx)"
lemma [simp]: "the_same_addr (base |+ ofs) (base' |+ ofs') \<longleftrightarrow> base = base' \<and> same_addr_offset base' ofs ofs'"
  unfolding the_same_addr_def by simp

lemma same_addr_offset_inj: "same_addr_offset seg p a1 \<and> same_addr_offset seg p a2 \<Longrightarrow> a1 = a2"
  by (auto simp add: same_addr_offset_def raw_offset_of_def raw_offset_of_inj)
lemma same_addr_offset_inj2: "same_addr_offset seg p1 a \<and> same_addr_offset seg p2 a \<Longrightarrow> p1 = p2"
  by (auto simp add: same_addr_offset_def raw_offset_of_def raw_offset_of_inj)

consts logical_offset_of :: "msegment \<Rightarrow> size_t word \<Rightarrow> nat"
specification (logical_offset_of)
  logical_offset_of[simp]: "same_addr_offset seg ofsp ofsx \<Longrightarrow> logical_offset_of seg ofsp = ofsx"
proof show "\<forall>ofsp ofsx seg. same_addr_offset seg ofsp ofsx \<longrightarrow>  (\<lambda>seg p. @x. same_addr_offset seg p x) seg ofsp = ofsx"
    using same_addr_offset_inj by blast qed

definition "logical_addr_of addrp = (case addrp of seg |+ ofsp \<Rightarrow> seg |+ logical_offset_of seg ofsp) "
lemma [simp]: "logical_addr_of (seg |+ ofsp) = seg |+ logical_offset_of seg ofsp"
  unfolding logical_addr_of_def by simp

(* definition addr'_allocated :: "heap \<Rightarrow> raw_memaddr \<Rightarrow> bool"
  where "addr'_allocated heap addr' \<longleftrightarrow> (\<exists>addr. the_same_addr addr' addr \<and> addr_allocated heap addr)" *)

(* instantiation memaddr :: ceq begin
definition ceqable_memaddr :: " heap \<Rightarrow> memaddr \<Rightarrow> memaddr \<Rightarrow> bool"
  where [simp]: "ceqable_memaddr heap x y = (addr_allocated heap x \<and> addr_allocated heap y)"
definition ceq_memaddr :: " memaddr \<Rightarrow> memaddr \<Rightarrow> bool" where [simp]: "ceq_memaddr = (=)"
instance by standard auto
end *)

instantiation memptr :: ceq begin
definition ceqable_memptr :: " heap \<Rightarrow> memptr \<Rightarrow> memptr \<Rightarrow> bool" where
  "ceqable_memptr heap x y = (case x of memptr a \<Rightarrow> case y of memptr b \<Rightarrow>
    (segment_of a = segment_of b))"
lemma [simp]: "ceqable heap (memptr a) (memptr b) \<longleftrightarrow>
  (segment_of a = segment_of b)"
  unfolding ceqable_memptr_def by simp
definition ceq_memptr :: " memptr \<Rightarrow> memptr \<Rightarrow> bool" where [simp]: "ceq_memptr = (=)"
instance proof
  fix x y z :: " memptr" and h :: heap
  show "ceqable h x y = ceqable h y x" by (cases x; cases y) auto
  show "ceqable h x x \<Longrightarrow> ceq x x" and "ceqable h x y \<Longrightarrow> ceq x y = ceq y x"
    and "ceqable h x y \<Longrightarrow> ceqable h y z \<Longrightarrow> ceqable h x z \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z" by auto+
qed
end

subsection \<open>\<nu>-abstraction\<close>

subsubsection \<open>Raw Pointer\<close>

definition RawPointer :: "(memptr, raw_memaddr) \<nu>"
  where "RawPointer x = { memptr i | i. i = x}"

lemma [simp]: "memptr i \<nuLinkL> RawPointer \<nuLinkR> i' \<longleftrightarrow> (i = i')" unfolding Refining_def by (simp add: RawPointer_def)
lemma [elim,\<nu>elim]: "addr \<ratio> RawPointer \<Longrightarrow> C \<Longrightarrow> C" unfolding Inhabited_def by (simp add: lrep_exps)
lemma [\<nu>intro 1]: "\<nu>Zero RawPointer undefined" unfolding \<nu>Zero_def by simp
lemma [\<nu>intro 1]: "\<nu>Equal RawPointer (\<lambda>x y. segment_of x = segment_of y) (=)" unfolding \<nu>Equal_def by (simp add: lrep_exps)

subsubsection \<open>Pointer\<close>

definition Pointer :: "(memptr, nat memaddr) \<nu>"
  where "Pointer x = { memptr raw | raw. the_same_addr raw x}"

lemma [simp]: "memptr raw \<nuLinkL> Pointer \<nuLinkR> addr \<longleftrightarrow> the_same_addr raw addr"
  unfolding Refining_def by (simp add: Pointer_def)
lemma [elim,\<nu>elim]: "addr \<ratio> Pointer \<Longrightarrow> C \<Longrightarrow> C" unfolding Inhabited_def by (simp add: lrep_exps)
lemma [\<nu>intro 1]: "\<nu>Equal Pointer (\<lambda>x y. segment_of x = segment_of y) (=)"
  unfolding \<nu>Equal_def using raw_offset_of_inj by (auto simp add: lrep_exps the_same_addr_def same_addr_offset_def)


subsubsection \<open>Casts\<close>

(* named_theorems fixtyp_\<nu>cast and freetyp_\<nu>cast

lemma [\<nu>intro, fixtyp_\<nu>cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e address_llty addr = ty \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t addr \<tycolon> Pointer['spc] \<longmapsto> addr \<tycolon> TypedPtr['spc::len0] ty"
  unfolding Cast_def by (cases addr) (auto simp add: lrep_exps split: memaddr.split)

lemma [\<nu>intro, freetyp_\<nu>cast]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t addr \<tycolon> TypedPtr['spc] ty \<longmapsto> addr \<tycolon> Pointer['spc::len0] \<^bold>w\<^bold>i\<^bold>t\<^bold>h address_llty addr = ty"
  unfolding Cast_def by (cases addr) (auto simp add: lrep_exps split: memaddr.split)
*)

section \<open>The integer data type\<close>

subsection \<open>Lrep instantiations\<close>

instantiation word :: (len) lrep begin
definition llty_word :: "'a word itself \<Rightarrow> llty" where [simp]: "llty_word _ = llty_int LENGTH('a)"
definition deepize_word :: " 'a word \<Rightarrow> deep_model " where "deepize_word x = DM_int LENGTH('a) (unat x)"
definition shallowize_word :: " deep_model \<Rightarrow> 'a word" where "shallowize_word x = (case x of DM_int _ n \<Rightarrow> of_nat n)"
instance apply standard using deepize_word_def shallowize_word_def by auto
end

instantiation word :: (len) ceq
begin
definition ceqable_word :: "heap \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> bool" where [simp]: "ceqable_word _ x y = True"
definition ceq_word :: "'a word \<Rightarrow>  'a word \<Rightarrow> bool" where [simp]: "ceq_word x y = (x = y)"
instance by standard (auto+)
end

instantiation word :: (len) field begin instance by standard end
instantiation word :: (len) field_list begin instance by standard end

subsection \<open>Basic \<nu>-abstractions based on integer type\<close>

subsubsection \<open>Natural number\<close>

definition NuNat :: "('a::len) itself \<Rightarrow> ('a word, nat) \<nu>" where "NuNat _ x = {p. unat p = x }"
syntax "_NuNat_" :: "type \<Rightarrow> logic" (\<open>\<nat>'[_']\<close>)
translations "\<nat>['x]" == "CONST NuNat (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuNat b \<nuLinkR> x \<equiv> (unat p = x)" unfolding Refining_def by (simp add: NuNat_def)
lemma [elim,\<nu>elim]: "x \<ratio> \<nat>['b::len] \<Longrightarrow> (x < 2^LENGTH('b) \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

lemma [\<nu>intro 1]: "\<nu>Equal (NuNat b) (\<lambda>x y. True) (=)"
  unfolding \<nu>Equal_def by (auto simp add: unsigned_word_eqI)
lemma [\<nu>intro 1]: "\<nu>Zero (NuNat b) 0" unfolding \<nu>Zero_def by simp

definition NuNatRound :: "('a::len) itself \<Rightarrow> ('a word, nat) \<nu>" where "NuNatRound _ x = {p. p = of_nat x}"
syntax "_NuNatRound_" :: "type \<Rightarrow> logic" (\<open>\<nat>\<^sup>r'[_']\<close>)
translations "\<nat>\<^sup>r['x]" == "CONST NuNatRound (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuNatRound b \<nuLinkR> x \<equiv> (p = of_nat x)" unfolding Refining_def  by (simp add: NuNatRound_def)
lemma [\<nu>intro 1]: "\<nu>Zero (NuNatRound b) 0" unfolding \<nu>Zero_def by simp


\<nu>processor literal_number 9500\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Parse.number >> (fn num => fn _ =>
  let open NuBasics
    val num = Syntax.parse_term ctx num
    fun mk term = mk_nuTy (num, term) |> Syntax.check_term ctx |> Thm.cterm_of ctx
    val term = ((stack_of_meta meta |> hd |> #2 |> mk)
      handle TERM _ => mk @{term \<open>\<nat>[32]\<close>}
        | ERROR _ => mk @{term \<open>\<nat>[32]\<close>}) |> @{print}
    val ctx = NuSys.load_specthm meta ctx
  in NuSys.auto_construct ctx term meta  end)
\<close>



subsubsection \<open>Integer\<close>

definition NuInt :: "('a::len) itself \<Rightarrow> ('a word, int) \<nu>" where "NuInt _ x = {p. sint p = x}"
syntax "_NuInt_" :: "type \<Rightarrow> logic" (\<open>\<int>'[_']\<close>)
translations "\<int>['x]" == "CONST NuInt (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuInt b \<nuLinkR> x \<equiv> (sint p = x)" unfolding Refining_def by (simp add: NuInt_def)
lemma [elim,\<nu>elim]: " x \<ratio> \<int>['b::len] \<Longrightarrow> (x < 2^(LENGTH('b) - 1) \<Longrightarrow> -(2^(LENGTH('b)-1)) \<le> x \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def apply simp by (metis One_nat_def sint_ge sint_lt) 

lemma [\<nu>intro 1]: "\<nu>Equal (NuInt b) (\<lambda>x y. True) (=)" unfolding \<nu>Equal_def by (auto simp add: signed_word_eqI) 
lemma [\<nu>intro 1]: "\<nu>Zero (NuInt b) 0" unfolding \<nu>Zero_def by simp

subsubsection \<open>Boolean\<close>

lemma [simp]: "(x \<noteq> 1) = (x = 0)" for x :: "1 word" proof -
  have "(UNIV:: 1 word set) = {0,1}" unfolding UNIV_word_eq_word_of_nat
  using less_2_cases apply auto apply force
  by (metis UNIV_I UNIV_word_eq_word_of_nat len_num1 power_one_right)
  then show ?thesis  by auto
qed

definition NuBool :: "(1 word, bool) \<nu>" ("\<bool>") where "NuBool x = {p. (p = 1) = x }"

lemma [simp]: " p \<nuLinkL> \<bool> \<nuLinkR> x \<longleftrightarrow> (p = 1) = x" unfolding Refining_def by (simp add: NuBool_def)
lemma [\<nu>intro 1]: "\<nu>Equal \<bool> (\<lambda>x y. True)  (=)" unfolding \<nu>Equal_def by auto
lemma [\<nu>intro 1]: "\<nu>Zero NuBool False" unfolding \<nu>Zero_def by simp

(* subsection \<open>Fusion \<nu>-abstraction\<close>


definition AutoFusion (infixr "\<nuFusion>''" 70)  where "AutoFusion = Fusion"
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuFusion> M \<longmapsto> x' \<tycolon> N' \<nuFusion> M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuFusion> M \<longmapsto> x' \<tycolon> N' \<nuFusion>' M' \<^bold>w\<^bold>i\<^bold>t\<^bold>h P"
  unfolding Cast_def AutoFusion_def . *)

section \<open>Tuple\<close>

datatype 'a tuple = Tuple "('a::field_list)"

lemma tuple_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>x. P (Tuple x))" by (metis tuple.exhaust) 
lemma tuple_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>x. P (Tuple x))" by (metis tuple.exhaust) 

subsection \<open>Lrep instantiations\<close>

subsubsection \<open>lrep\<close>

instantiation tuple :: (field_list) lrep begin
definition llty_tuple :: " 'a tuple itself \<Rightarrow> llty " where [simp]: "llty_tuple _ = llty_tup (llty TYPE('a))"
definition deepize_tuple :: " 'a tuple \<Rightarrow> deep_model " where "deepize_tuple x = DM_record (deepize (case_tuple id x))"
definition shallowize_tuple :: " deep_model \<Rightarrow> 'a tuple " where "shallowize_tuple x = (case x of DM_record y \<Rightarrow> Tuple (shallowize y))"
instance apply standard using shallowize_tuple_def deepize_tuple_def by (auto split: tuple.split)
end

subsubsection \<open>zero\<close>

instantiation tuple :: ("{zero,field_list}") zero begin
definition zero_tuple :: " 'a tuple " where [simp]: "zero_tuple = Tuple 0"
instance by standard
end

subsubsection \<open>ceq\<close>

instantiation tuple :: ("{ceq,field_list}") ceq begin
definition ceqable_tuple :: " heap \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> bool " where "ceqable_tuple heap = rel_tuple (ceqable heap)"
definition ceq_tuple :: " 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> bool " where "ceq_tuple = rel_tuple ceq"
lemma [simp]: "ceqable heap (Tuple a) (Tuple b) = ceqable heap a b" unfolding ceqable_tuple_def by simp
lemma [simp]: "ceq (Tuple a) (Tuple b) = ceq a b" unfolding ceq_tuple_def by simp
instance proof
  fix x y z :: " 'a tuple" and h :: heap
  show "ceqable h x y = ceqable h y x" by (cases x; cases y) simp
  show "ceqable h x x \<Longrightarrow> ceq x x" by (cases x) auto
  show "ceqable h x y \<Longrightarrow> ceq x y = ceq y x" by (cases x; cases y) simp
  show "ceqable h x y \<Longrightarrow> ceqable h y z \<Longrightarrow> ceqable h x z \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z" by (cases x, cases y, cases z) (simp, blast intro: ceq_trans)
qed
end

subsubsection \<open>miscellaneous\<close>

instantiation tuple :: (field_list) field begin instance by standard end
instantiation tuple :: (field_list) field_list begin instance by standard end

subsection \<open>Nu abstraction - `NuTuple`\<close>

definition NuTuple :: "(('a::field_list), 'b) \<nu> \<Rightarrow> ('a tuple, 'b) \<nu>" ("\<lbrace> _ \<rbrace>") where "\<lbrace> N \<rbrace> x = { Tuple p | p. p \<nuLinkL> N \<nuLinkR> x}"

lemma [simp]: "Tuple p \<nuLinkL> \<lbrace> N \<rbrace> \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> N \<nuLinkR> x" by (simp add: lrep_exps NuTuple_def Refining_def)
lemma [elim,\<nu>elim]: "x \<ratio> \<lbrace> N \<rbrace> \<Longrightarrow> (x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def tuple_exists by simp

lemma [\<nu>intro 1]: "\<nu>Equal N P eq \<Longrightarrow> \<nu>Equal \<lbrace> N \<rbrace> P eq" unfolding \<nu>Equal_def tuple_forall by simp
lemma [\<nu>intro 1]: "\<nu>Zero N z \<Longrightarrow> \<nu>Zero \<lbrace> N \<rbrace> z" unfolding \<nu>Zero_def by simp

section \<open>Function Pointer\<close>

subsubsection \<open>lrep\<close>

instantiation fun_addr ::  lrep begin
definition llty_fun_addr :: " fun_addr itself \<Rightarrow> llty " where [simp]: "llty_fun_addr _ = Lty_fun_addr"
definition deepize_fun_addr :: " fun_addr \<Rightarrow> deep_model " where "deepize_fun_addr = DM_fun_addr"
definition shallowize_fun_addr :: " deep_model \<Rightarrow> fun_addr " where "shallowize_fun_addr x = (case x of DM_fun_addr y \<Rightarrow> y)"
instance apply standard using shallowize_fun_addr_def deepize_fun_addr_def by auto
end

subsubsection \<open>zero\<close>

instantiation fun_addr :: zero begin
definition zero_fun_addr :: " fun_addr " where "zero_fun_addr = fun_addr_NULL"
instance by standard
end

subsubsection \<open>ceq\<close>

instantiation fun_addr :: ceq begin
definition ceqable_fun_addr :: " heap \<Rightarrow> fun_addr \<Rightarrow> fun_addr \<Rightarrow> bool " where [simp]: "ceqable_fun_addr _ _ _ = True"
definition ceq_fun_addr :: " fun_addr \<Rightarrow> fun_addr \<Rightarrow> bool " where [simp]: "ceq_fun_addr = (=)"
instance by standard auto
end

subsubsection \<open>miscellaneous\<close>

instantiation fun_addr :: field begin instance by standard end
instantiation fun_addr :: field_list begin instance by standard end

subsubsection \<open>\<nu>-abstractor\<close>

definition op_func_pointer :: "('a \<longmapsto> 'b) \<Rightarrow> ('r :: stack) \<longmapsto> (fun_addr \<times> 'r)"
  where "op_func_pointer f = (\<lambda>(h,r).
    if (\<exists>a. fun_table a = Some f)
    then Success (h, (SOME a. fun_table a = Some f), r)
    else PartialCorrect
)"

definition FunPtr :: "(heap \<times> 'ap::lrep,'ax) \<nu> \<Rightarrow> (heap \<times> 'bp::lrep,'bx) \<nu> \<Rightarrow> (fun_addr, 'ax \<longmapsto> 'bx) \<nu>"
  where "FunPtr A B fx  = {faddr. (\<exists>fp. fun_table faddr = Some fp \<and> (\<forall>a b. \<^bold>p\<^bold>r\<^bold>o\<^bold>c fp \<blangle> a \<tycolon> A \<longmapsto> b \<tycolon> B \<brangle>))}"

end