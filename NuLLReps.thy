theory NuLLReps
  imports NuSys "HOL-Library.Word"
  abbrevs "<own>" = "\<left_fish_tail>"
    and "<none>" = "\<down_fish_tail>"
    and "<object>" = "\<R_arr_tail>"
begin   

section \<open>\<phi>-Types for Semantic Models\<close>

declare pair_forall[lrep_exps] pair_exists[lrep_exps]
(* declare llty_prod[\<phi>intro] *)

context std begin

subsection \<open>Integer\<close>

subsubsection \<open>Natural Nmbers\<close>

paragraph \<open>Natural Number\<close>

definition \<phi>Nat :: "nat \<Rightarrow> ('VAL, nat) \<phi>" ("\<nat>[_]")
  where "\<nat>[b] x = (if x < 2^b then { V_int.mk (\<phi>word b x) } else {})"

lemma \<phi>Nat_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>[b]) \<longleftrightarrow> (p = V_int.mk (\<phi>word b x)) \<and> x < 2^b"
  unfolding \<phi>Type_def by (simp add: \<phi>Nat_def)

lemma \<phi>Nat_elim[elim!,\<phi>elim]:
  "Inhabited (x \<Ztypecolon> \<nat>[b]) \<Longrightarrow> (x < 2^b \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (auto simp add: \<phi>expns)

lemma [\<phi>reason on \<open>\<phi>Equal (\<nat>[?b]) ?c ?eq\<close>]:
  "\<phi>Equal (\<nat>[b]) (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (auto simp add: unsigned_word_eqI \<phi>expns)

lemma [\<phi>reason on \<open>\<phi>Zero (T_int.mk ?b) (\<nat>[?b]) ?zero\<close>]:
  "\<phi>Zero (T_int.mk b) (\<nat>[b]) 0" unfolding \<phi>Zero_def by (simp add: \<phi>expns)

\<phi>processor literal_number 9500\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>
  \<open>fn ctx => fn meta => Parse.number >> (fn num => fn _ =>
  let open NuBasics
    val num = Syntax.parse_term ctx num
    fun mk term = mk_nuTy (num, term) |> Syntax.check_term ctx |> Thm.cterm_of ctx
    val term = (
        (dest_current_nu meta |> strip_separations |> hd |> dest_RepSet |> #2 |> mk)
      handle TERM _ => mk @{term \<open>\<nat>[32]\<close>}
        | ERROR _ => mk @{term \<open>\<nat>[32]\<close>})
  in (NuSys.auto_construct ctx term meta, ctx)  end)
\<close>

paragraph \<open>Rounded Natural Number\<close>

definition \<phi>NatRound :: "nat \<Rightarrow> ('VAL, nat) \<phi>" ("\<nat>\<^sup>r[_]")
  where "\<nat>\<^sup>r[b] x = { V_int.mk (\<phi>word b (x mod 2^b)) }"

lemma \<phi>NatRound_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<nat>\<^sup>r[b]) \<longleftrightarrow> p = V_int.mk (\<phi>word b (x mod 2^b))"
  unfolding \<phi>Type_def \<phi>NatRound_def by simp

lemma [\<phi>reason on \<open>\<phi>Zero (T_int.mk ?b) \<nat>\<^sup>r[?b] ?z\<close>]:
  "\<phi>Zero (T_int.mk b) (\<nat>\<^sup>r[b]) 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)


paragraph \<open>Integer in the normal sense\<close>


definition \<phi>Int :: "nat \<Rightarrow> ('VAL, int) \<phi>" ("\<int>[_]")
  where "\<phi>Int b x =(if x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0)
                    then { V_int.mk (\<phi>word b (if x \<ge> 0 then nat x else nat (2^b + x))) }
                    else {})"

lemma \<phi>Int_expn[\<phi>expns]:
  "p \<in> (x \<Ztypecolon> \<int>[b]) \<longleftrightarrow> p = V_int.mk (\<phi>word b (if x \<ge> 0 then nat x else nat (2^b + x)))
                      \<and> x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0)"
  unfolding \<phi>Type_def by (simp add: \<phi>Int_def)

lemma \<phi>Int_inhabited[elim,\<phi>elim]:
  "Inhabited (x \<Ztypecolon> \<int>[b]) \<Longrightarrow> (x < 2^(b - 1) \<and> -(2^(b-1)) \<le> x \<and> (b = 0 \<longrightarrow> x = 0) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns) 


lemma [simp]: \<open>- (2^(b - 1)) \<le> x \<Longrightarrow> 0 \<le> 2 ^ b + x\<close> for x :: int
  by (smt (verit, best) diff_le_self power_increasing_iff)

lemma [\<phi>reason on \<open>\<phi>Equal \<int>[b] ?c ?eq\<close>]:
    "\<phi>Equal \<int>[b] (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (cases b) (auto simp add: \<phi>expns eq_nat_nat_iff)

lemma [\<phi>reason on \<open>\<phi>Zero (T_int.mk ?b) \<int>[?b] ?x\<close>]:
    "\<phi>Zero (T_int.mk b) \<int>[b] 0"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)


paragraph \<open>Boolean\<close>

(* lemma [simp]: "(x \<noteq> 1) = (x = 0)" for x :: "1 word" proof -
  have "(UNIV:: 1 word set) = {0,1}" unfolding UNIV_word_eq_word_of_nat
  using less_2_cases apply auto apply force
  by (metis UNIV_I UNIV_word_eq_word_of_nat len_num1 power_one_right)
  then show ?thesis  by auto
qed *)

definition \<phi>Bool :: "('VAL, bool) \<phi>" ("\<bool>")
  where "\<bool> x = { V_int.mk (\<phi>word 1 (if x then 1 else 0)) }"

lemma \<phi>Bool_expn[\<phi>expns]:
  " p \<in> (x \<Ztypecolon> \<bool>) \<longleftrightarrow> p = V_int.mk (\<phi>word 1 (if x then 1 else 0))"
  unfolding \<phi>Type_def \<phi>Bool_def by simp

lemma \<phi>Bool_inhabited[\<phi>elim, elim!]:
  \<open>Inhabited (x \<Ztypecolon> \<bool>) \<Longrightarrow> C \<Longrightarrow> C\<close> .

lemma \<phi>Bool_eqcmp[\<phi>reason on \<open>\<phi>Equal \<bool> ?c ?eq\<close>]:
  "\<phi>Equal \<bool> (\<lambda>x y. True) (=)"
  unfolding \<phi>Equal_def by (simp add: \<phi>expns)

lemma \<phi>Bool_zero[\<phi>reason on \<open>\<phi>Zero (\<tau>Int 1) \<bool> ?z\<close>]:
  "\<phi>Zero (\<tau>Int 1) \<bool> False"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)


subsection \<open>Pointers\<close>

subsubsection \<open>Raw Pointer\<close>

definition RawPointer :: "('VAL, 'TY rawaddr) \<phi>"
  where "RawPointer x = (if Valid_Address x then { V_pointer.mk x } else {})"

lemma RawPointer_expn[\<phi>expns]:
  "v \<in> (p \<Ztypecolon> RawPointer) \<longleftrightarrow> v = V_pointer.mk p \<and> Valid_Address p"
  by (simp add: \<phi>Type_def RawPointer_def \<phi>expns)

lemma RawPointer_inhabited[elim,\<phi>elim]:
  "Inhabited (p \<Ztypecolon> RawPointer) \<Longrightarrow> (Valid_Address p \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma RawPointer_zero[\<phi>reason on \<open>\<phi>Zero (T_pointer.mk ()) RawPointer ?x\<close>]:
  "\<phi>Zero (T_pointer.mk ()) RawPointer (0 |: 0)"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns zero_memaddr_def Valid_Segment_zero)

lemma RawPointer_eqcmp[\<phi>reason on \<open>\<phi>Equal RawPointer ?c ?eq\<close>]:
  "\<phi>Equal RawPointer (\<lambda>x y. memaddr.segment x = memaddr.segment y) (=)"
  unfolding \<phi>Equal_def by (simp add: lrep_exps \<phi>expns)


subsubsection \<open>Pointer\<close>


definition (in std_sem) valid_logaddr :: "'TY logaddr \<Rightarrow> bool"
  where "valid_logaddr addr \<longleftrightarrow>
    Valid_Segment (memaddr.segment addr) \<and>
    memaddr.segment addr \<noteq> Null \<and>
    memaddr.offset addr \<le> segidx.len (memaddr.segment addr)"

definition (in std_sem) raw_offset_of :: "'TY segidx \<Rightarrow> nat \<Rightarrow> size_t"
  where "raw_offset_of seg i = of_nat (i * MemObj_Size (segidx.layout seg))"

lemma raw_offset_of_0[simp]: "raw_offset_of seg 0 = 0" unfolding raw_offset_of_def by auto

lemma (in std_sem) raw_offset_of_delta[simp]:
  "raw_offset_of seg (ofs + unat delta) = raw_offset_of seg ofs + delta * word_of_nat (MemObj_Size (segidx.layout seg))"
  unfolding raw_offset_of_def using distrib_right by auto

lemma (in std_sem) raw_offset_of_inj:
  "valid_logaddr (seg |: ofs1) \<Longrightarrow> valid_logaddr (seg |: ofs2) \<Longrightarrow>
    0 < MemObj_Size (segidx.layout seg) \<Longrightarrow>
    raw_offset_of seg ofs1 = raw_offset_of seg ofs2 \<Longrightarrow> ofs1 = ofs2"
  unfolding raw_offset_of_def word_of_nat_eq_iff take_bit_nat_def valid_logaddr_def Valid_Segment_def
  by (cases seg; simp)
     (smt (verit, best) mod_less mult.commute mult_cancel2 nat_less_le nat_mult_le_cancel1 order.strict_trans1)

lemma same_addr_offset_inj: "same_addr_offset seg p a1 \<and> same_addr_offset seg p a2 \<Longrightarrow> a1 = a2"
  by (auto simp add: same_addr_offset_def raw_offset_of_def raw_offset_of_inj)
lemma same_addr_offset_inj2: "same_addr_offset seg p1 a \<and> same_addr_offset seg p2 a \<Longrightarrow> p1 = p2"
  by (auto simp add: same_addr_offset_def raw_offset_of_def raw_offset_of_inj)


definition (in std_sem) same_addr_offset :: "'TY segidx \<Rightarrow> size_t \<Rightarrow> nat \<Rightarrow> bool"
  where "same_addr_offset seg ofsp ofsx \<longleftrightarrow> valid_logaddr (seg |: ofsx) \<and> raw_offset_of seg ofsx = ofsp"
definition the_same_addr :: "raw_memaddr \<Rightarrow> nat memaddr \<Rightarrow> bool"
  where "the_same_addr addrp addrx \<equiv>
    segment_of addrp = segment_of addrx
    \<and> same_addr_offset (segment_of addrx)  (offset_of addrp) (offset_of addrx)"
lemma [simp]: "the_same_addr (base |+ ofs) (base' |+ ofs') \<longleftrightarrow> base = base' \<and> same_addr_offset base' ofs ofs'"
  unfolding the_same_addr_def by simp




definition Pointer :: "('VAL, nat logaddr) \<phi>"
  where "Pointer x = { memptr raw | raw. the_same_addr raw x}"

lemma [\<phi>expns]: "memptr raw \<in> (addr \<tycolon> Pointer) \<longleftrightarrow> the_same_addr raw addr"
  unfolding \<phi>Type_def by (simp add: Pointer_def)
lemma [elim,\<phi>elim]: "addr \<ratio> Pointer \<Longrightarrow> C \<Longrightarrow> C" unfolding Inhabited_def by (simp add: lrep_exps)
lemma [\<phi>reason on \<open>\<phi>Equal Pointer ?c ?eq\<close>]:
    "\<phi>Equal Pointer (\<lambda>x y. segment_of x = segment_of y) (=)"
  unfolding \<phi>Equal_def using raw_offset_of_inj by (simp add: lrep_exps the_same_addr_def same_addr_offset_def \<phi>expns) blast
lemma [\<phi>reason on \<open>\<phi>Zero Pointer ?x\<close>]:
    "\<phi>Zero Pointer (undefined |+ 0)"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns same_addr_offset_def)



subsection \<open>Tuple Field\<close>

definition \<phi>Field :: "('VAL, 'a) \<phi> \<Rightarrow> ('VAL, 'a) \<phi>" ("\<clubsuit>")
  where "\<phi>Field T x = { V_tup.mk [v] |v. v \<in> T x }"

lemma \<phi>Field_expn[\<phi>expns]:
  \<open>p \<in> (x \<Ztypecolon> \<phi>Field T) \<longleftrightarrow> (\<exists>v. p = V_tup.mk [v] \<and> v \<in> (x \<Ztypecolon> T))\<close>
  unfolding \<phi>Field_def \<phi>Type_def by simp

lemma \<phi>Field_inhabited[elim,\<phi>elim]:
  \<open>Inhabited (x \<Ztypecolon> \<clubsuit> T) \<Longrightarrow> (Inhabited (x \<Ztypecolon> T) \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma \<phi>Field_zero  [\<phi>reason on \<open>\<phi>Zero (T_tup.mk [?ty]) (\<phi>Field ?T) ?x\<close>]:
  \<open>\<phi>Zero ty T x \<Longrightarrow> \<phi>Zero (T_tup.mk [ty]) (\<clubsuit> T) x \<close>
  unfolding \<phi>Zero_def by (simp add: \<phi>expns)

lemma \<phi>Field_zeros [\<phi>reason on \<open>\<phi>Zero (T_tup.mk [?ty]) (\<phi>Field ?T) ?x\<close>]:
  \<open>\<phi>Zero ty T x
    \<Longrightarrow> \<phi>Zero (T_tup.mk tys) (\<clubsuit> Ts) xs
    \<Longrightarrow> \<phi>Zero (T_tup.mk (ty#tys)) (\<clubsuit> T \<^emph> \<clubsuit> Ts) (x,xs) \<close>
  unfolding \<phi>Zero_def
  by (simp add: \<phi>expns V_tup_mult) (metis Cons_eq_append_conv V_tup_mult)


end




















section \<open>Memory address\<close>

text \<open>The concept of the address space is one of the notions in the LLVM\<close>

(* primrec addr_cap \<comment> \<open>The memory block starting at the address has length `len`\<close>
  where "addr_cap (seg |+ ofs) len \<longleftrightarrow> ofs = 0 \<and> segment_len seg = len" *)

(* definition "malloc h = (@x. \<forall>ofs. h (x |: ofs) = None)"

lemma malloc: "Heap h \<Longrightarrow> h (MemAddress (malloc h |+ ofs)) = None"
  unfolding Heap_def AvailableSegments_def malloc_def
  by (metis (mono_tags, lifting) not_finite_existsD tfl_some) 

lemma malloc2: "Heap h \<Longrightarrow> MemAddress (malloc h |+ ofs) \<notin> dom h"
  using malloc by (simp add: domIff) 


type_synonym raw_memaddr = "size_t word memaddr"
type_synonym logical_memaddr = "nat memaddr"

*)


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
definition deepize_memptr :: " memptr \<Rightarrow> value"
  where "deepize_memptr ptr = DM_pointer (case_memptr (map_memaddr unat) ptr)"
definition shallowize_memptr :: " value \<Rightarrow> memptr "
  where "shallowize_memptr dm = (case dm of DM_pointer addr \<Rightarrow> memptr (map_memaddr of_nat addr))"
instance apply standard subgoal for x apply (cases x) subgoal for xa apply (cases xa)
      by (auto simp add: shallowize_memptr_def deepize_memptr_def) done done 
end

instantiation memptr :: field begin instance by standard end
instantiation memptr :: field_list begin instance by standard end

instantiation memptr :: zero begin
definition zero_memptr :: " memptr" where [simp]: "zero_memptr = memptr (undefined |+ 0)"
instance by standard
end



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
lemma [simp]:
  "ceqable heap (memptr a) (memptr b) \<longleftrightarrow> (segment_of a = segment_of b)"
  unfolding ceqable_memptr_def by simp
definition ceq_memptr :: " memptr \<Rightarrow> memptr \<Rightarrow> bool" where [simp]: "ceq_memptr = (=)"
instance proof
  fix x y z :: " memptr" and h :: "heap"
  show "ceqable h x y = ceqable h y x" by (cases x; cases y) auto
  show "ceqable h x x \<Longrightarrow> ceq x x" and "ceqable h x y \<Longrightarrow> ceq x y = ceq y x"
    and "ceqable h x y \<Longrightarrow> ceqable h y z \<Longrightarrow> ceqable h x z \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z" by auto+
qed
end

subsection \<open>\<phi>-abstraction\<close>



subsubsection \<open>Casts\<close>

(* named_theorems fixtyp_\<phi>cast and freetyp_\<phi>cast

lemma [\<phi>intro, fixtyp_\<phi>cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e address_llty addr = ty \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t addr \<tycolon> Pointer['spc] \<longmapsto> addr \<tycolon> TypedPtr['spc::len0] ty"
  unfolding Cast_def by (cases addr) (auto simp add: lrep_exps split: memaddr.split)

lemma [\<phi>intro, freetyp_\<phi>cast]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t addr \<tycolon> TypedPtr['spc] ty \<longmapsto> addr \<tycolon> Pointer['spc::len0] \<^bold>w\<^bold>i\<^bold>t\<^bold>h address_llty addr = ty"
  unfolding Cast_def by (cases addr) (auto simp add: lrep_exps split: memaddr.split)
*)


subsubsection \<open>Index\<close>

definition index_tuple :: "('a,'b,'x,'y) index \<Rightarrow> ('a::field_list tuple, 'b::field_list tuple, 'x, 'y) index"
  where "index_tuple idx = (case idx of Index g m \<Rightarrow> Index (g o dest_tuple) (map_tuple o m))"

lemma [\<phi>reason]: "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<brangle>"
  unfolding \<phi>index_def index_tuple_def tuple_forall by (cases idx) (simp add: \<phi>expns)

lemma [\<phi>reason]:
    "\<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x idx \<blangle> X \<^bold>@ a \<tycolon> A \<longmapsto> Y \<^bold>@ b \<tycolon> B\<brangle> \<Longrightarrow> \<^bold>i\<^bold>n\<^bold>d\<^bold>e\<^bold>x index_tuple idx \<blangle> X \<^bold>@ a \<tycolon> \<lbrace> A \<rbrace> \<longmapsto> Y \<^bold>@ b \<tycolon> \<lbrace> B \<rbrace> \<brangle>"
  unfolding \<phi>index_def index_tuple_def tuple_forall by (cases idx) (simp add: \<phi>expns)

(*section \<open>Function Pointer\<close>

subsubsection \<open>lrep\<close>

instantiation fun_addr ::  lrep begin
definition llty_fun_addr :: " fun_addr itself \<Rightarrow> llty " where [simp, \<phi>reason]: "llty_fun_addr _ = Lty_fun_addr"
definition deepize_fun_addr :: " fun_addr \<Rightarrow> value " where "deepize_fun_addr = DM_fun_addr"
definition shallowize_fun_addr :: " value \<Rightarrow> fun_addr " where "shallowize_fun_addr x = (case x of DM_fun_addr y \<Rightarrow> y)"
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

subsubsection \<open>\<phi>-abstractor\<close>

definition op_func_pointer :: "('a \<longmapsto> 'b) \<Rightarrow> ('r :: stack) \<longmapsto> (fun_addr \<times> 'r)"
  where "op_func_pointer f = (\<lambda>(h,r).
    if (\<exists>a. fun_table a = Some f)
    then Success (h, (SOME a. fun_table a = Some f), r)
    else PartialCorrect
)"

definition FunPtr :: "(heap \<times> 'ap::lrep,'ax) \<phi> \<Rightarrow> (heap \<times> 'bp::lrep,'bx) \<phi> \<Rightarrow> (fun_addr, 'ax \<longmapsto> 'bx) \<phi>"
  where "FunPtr A B fx  = {faddr. (\<exists>fp. fun_table faddr = Some fp \<and> (\<forall>a b. \<^bold>p\<^bold>r\<^bold>o\<^bold>c fp \<blangle> a \<tycolon> A \<longmapsto> b \<tycolon> B \<brangle>))}" *)

end