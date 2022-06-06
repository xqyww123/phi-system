(* KEEP IT SIMPLE AND STUPID *)

theory NuPrime \<comment> \<open>The Primary Theory of the \<phi>-System\<close>
  imports Main
    "HOL-Library.Word"
    NoePreliminary
    "HOL-Library.Adhoc_Overloading"
    Fictional_Algebra
    "Virt_Datatype/Virtual_Datatype"
  abbrevs "<:>" = "\<Ztypecolon>"
begin

section \<open>Semantic Framework\<close>

subsection\<open>Semantic Models\<close>

subsubsection \<open>Global Parameter\<close>

consts addrspace_bits :: "nat" \<comment> \<open>The bit length of the memory address space, in unit of bits\<close>
specification (addrspace_bits) addrspace_bits_L0: "0 < addrspace_bits" by auto


subsubsection \<open>Type\<close>

virtual_datatype std_ty =
  T_int     :: nat \<comment> \<open>in unit of bits\<close>
  T_pointer :: unit
  T_tup     :: \<open>'self list\<close>
  T_array   :: \<open>'self \<times> nat\<close>

context std_ty begin
abbreviation \<open>\<tau>Int \<equiv> T_int.mk\<close>
abbreviation \<open>\<tau>Pointer \<equiv> T_pointer.mk ()\<close>
abbreviation \<open>\<tau>Tuple \<equiv> T_tup.mk\<close>
abbreviation \<open>\<tau>Array N T \<equiv> T_array.mk (T,N)\<close>
end

(* datatype llty = T_int nat \<comment> \<open>int bits\<close> | T_pointer | T_tup llty
  | T_array llty nat | T_nil *)


subsubsection \<open>Value\<close>

paragraph \<open>Memory Address\<close>

typedecl addr_cap

instantiation addr_cap :: len begin
definition [simp]: "len_of_addr_cap (_::addr_cap itself) = addrspace_bits"
instance apply standard using addrspace_bits_L0 by simp
end

type_synonym size_t = \<open>addr_cap word\<close>


datatype ('TY) segidx = Null | Segment nat \<comment> \<open>nonce\<close> (layout: 'TY)
declare segidx.map_id0[simp]

hide_const (open) layout

datatype 'TY memaddr = memaddr (segment: "'TY segidx") (index: \<open>nat list\<close> ) (infixl "|:" 60)
declare memaddr.sel[iff]
hide_const (open) segment index

type_synonym 'TY logaddr = "'TY memaddr" (* the index of logaddr is non empty *)
type_synonym 'TY rawaddr = \<open>'TY logaddr \<times> size_t\<close>

instantiation segidx :: (type) zero begin
definition "zero_segidx = Null"
instance ..
end

instantiation memaddr :: (type) zero begin
definition "zero_memaddr = (0 |: 0)"
instance ..
end



abbreviation shift_addr :: "'TY logaddr \<Rightarrow> nat \<Rightarrow> 'TY logaddr" (infixl "||+" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. x + delta) id addr"
lemma memaddr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>base ofs. P (base |: ofs))" by (metis memaddr.exhaust)
lemma memaddr_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>base ofs. P (base |: ofs))" by (metis memaddr.exhaust)

lemma mem_shift_shift[simp]: "a ||+ i ||+ j = a ||+ (i + j)" for i :: nat by (cases a) simp





paragraph \<open>Model\<close>

virtual_datatype 'TY std_val :: nonsepable_semigroup =
  V_int     :: \<open>nat \<times> nat\<close>
  V_pointer :: \<open>'TY rawaddr\<close>
  V_tup     :: \<open>'self list\<close>
  V_array   :: \<open>'TY \<times> 'self list\<close>

virtual_datatype 'TY std_shared_val :: sep_algebra =
  SV_int     :: \<open>nat \<times> nat share option\<close>
  SV_pointer :: \<open>'TY rawaddr share option\<close>
  SV_tup     :: \<open>'self list\<close>
  SV_array   :: \<open>'TY \<times> 'self list\<close>


subsubsection \<open>Resource\<close>

type_synonym 'v opstack = "'v list"
type_synonym varname = nat
type_synonym ('TY,'VAL) R_mem' = \<open>('TY segidx \<rightharpoonup> 'VAL)\<close>
type_synonym ('TY,'VAL) R_mem = \<open>('TY,'VAL) R_mem' ?\<close>
type_synonym ('TY,'VAL) R_var = \<open>(string \<rightharpoonup> 'VAL) ?\<close>

resource_space ('VAL::nonsepable_semigroup,'TY) std_res =
  R_mem :: \<open>('TY,'VAL) R_mem\<close>
  R_var :: \<open>('TY,'VAL) R_var\<close>

paragraph \<open>Valid Memory\<close>

definition Available_Segments :: "('TY,'VAL) R_mem' \<Rightarrow> 'TY segidx set"
  where "Available_Segments heap = {seg. heap seg = None}"

definition Valid_Mem :: "('TY,'VAL) R_mem set"
  where "Valid_Mem = { Fine h |h. infinite (Available_Segments h) }"

(* lemma 
  assumes A: "h \<in> Valid_Mem"
  shows GoodMem_upd[intro]: "h(k := v)\<^sub>? \<in> Valid_Mem"
proof -
  obtain h' where h: "h = Fine h'" and inf: "infinite (Available_Segments h')"
    using A unfolding Valid_Mem_def by blast
  have "Available_Segments h' \<subseteq> {(case k of (seg |: ofs) \<Rightarrow> seg)} \<union> (Available_Segments (h'(k := v)))"
    unfolding Available_Segments_def by auto 
  then show ?thesis
    using Valid_Mem_def finite_subset h inf by fastforc
qed *)

(* lemma
  assumes S: "!! h' \<subseteq>\<^sub>m !! h"
    and A: "h \<in> GoodMem"
  shows Heap_subset: "h' \<in> GoodMem "
proof -
  obtain H where h: "h = Fine H" and inf: "infinite (AvailableSegments H)"
    using A unfolding GoodMem_def by blast
  have "AvailableSegments h \<subseteq> AvailableSegments h'"
    unfolding AvailableSegments_def using prems(1)
    by (smt (verit, best) Collect_mono domIff map_le_def)
  then show ?thesis using prems(2) using finite_subset by blas
qed done

lemma Heap_map_add: "Heap (h1 ++ h2) \<Longrightarrow> Heap h2"
  using Heap_subset map_le_map_add by blast

lemma Heap_restrict[intro]: "Heap h \<Longrightarrow> Heap (h |` S)"
  by (metis domIff map_le_def restrict_map_def Heap_subset

*)

subsection \<open>A Standard Semantics\<close>

locale std_sem_pre =
  std_ty  where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ std_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ std_res where TYPE'VAL  = \<open>TYPE('VAL)\<close>
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('RES_N)\<close>
            and TYPE'REP  = \<open>TYPE('RES::comm_monoid_mult)\<close>
  for TY_CONS_OF and VAL_CONS_OF
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N => 'VAL) \<times> ('RES_N => 'RES)) itself\<close>

  assumes V_tup_mult: \<open>V_tup.mk t1 * V_tup.mk t2 = V_tup.mk (t1 @ t2)\<close>
  fixes MemObj_Size :: \<open>'TY \<Rightarrow> nat\<close> \<comment> \<open>in size of bytes\<close>
    and valid_idx_step :: \<open>'TY \<Rightarrow> nat \<Rightarrow> bool\<close>
    and idx_step_type   :: \<open>nat \<Rightarrow> 'TY \<Rightarrow> 'TY\<close>
    and idx_step_value  :: \<open>nat \<Rightarrow> 'VAL \<Rightarrow> 'VAL\<close>
    and idx_step_mod_value :: \<open>nat \<Rightarrow> ('VAL \<Rightarrow> 'VAL) \<Rightarrow> 'VAL \<Rightarrow> 'VAL\<close>
    and idx_step_offset :: \<open>'TY \<Rightarrow> nat \<Rightarrow> nat\<close>
(*  assumes MemObj_Size_L0[simp]: \<open>0 < MemObj_Size x\<close>
     *)
  assumes memobj_size_arr    : \<open>MemObj_Size (\<tau>Array N T) = N * MemObj_Size T\<close>
    and   memobj_size_step   : \<open>valid_idx_step T i \<Longrightarrow> MemObj_Size (idx_step_type i T) \<le> MemObj_Size T\<close>
    and   idx_step_type_tup  : \<open>i < length tys \<Longrightarrow> idx_step_type i (\<tau>Tuple tys) = tys!i \<close>
    and   idx_step_type_arr  : \<open>i < N \<Longrightarrow> idx_step_type i (\<tau>Array N T) = T\<close>
    and   valid_idx_step_tup : \<open>valid_idx_step (\<tau>Tuple tys) i \<longleftrightarrow> i < length tys\<close>
    and   valid_idx_step_arr : \<open>valid_idx_step (\<tau>Array N T) i \<longleftrightarrow> i < N\<close>
    and   idx_step_value_tup : \<open>idx_step_value i (V_tup.mk vs)   = vs!i\<close>
    and   idx_step_value_arr : \<open>idx_step_value i (V_array.mk (T,vs)) = vs!i\<close>
    and   idx_step_mod_value_tup : \<open>idx_step_mod_value i f (V_tup.mk vs)   = V_tup.mk   (vs[i := f (vs!i)])\<close>
    and   idx_step_mod_value_arr : \<open>idx_step_mod_value i f (V_array.mk (T,vs)) = V_array.mk (T,vs[i := f (vs!i)])\<close>
    and   idx_step_offset_arr: \<open>idx_step_offset (\<tau>Array N T) i = i * MemObj_Size T\<close>
    and   idx_step_offset_step:\<open>valid_idx_step T i \<Longrightarrow> idx_step_offset T i \<le> MemObj_Size T\<close>
    and   idx_step_offset_inj: \<open>valid_idx_step T i \<Longrightarrow> valid_idx_step T j \<Longrightarrow> idx_step_offset T i = idx_step_offset T j \<Longrightarrow> i = j\<close>
      \<comment> \<open>It may introduce a restriction: types like zero-element tuple and array must occupy at
          least 1 byte, which may affect the performance unnecessarily. However, since zero-element
          tuple and array are so special  \<close>
begin

abbreviation \<open>type_storable_in_mem T \<equiv> MemObj_Size T < 2^addrspace_bits\<close>

definition \<open>Valid_Segment seg = (
    case seg of Null \<Rightarrow> True
              | Segment _ ty \<Rightarrow> type_storable_in_mem ty
    )\<close>

lemma Valid_Segment_zero: \<open>Valid_Segment 0\<close>
  unfolding Valid_Segment_def zero_segidx_def by simp


abbreviation \<open>index_value \<equiv> foldr idx_step_value\<close>
abbreviation \<open>index_type  \<equiv> foldr idx_step_type\<close>
abbreviation \<open>index_mod_value \<equiv> foldr idx_step_mod_value\<close>

primrec valid_index :: \<open>'TY \<Rightarrow> nat list \<Rightarrow> bool\<close>
  where \<open>valid_index T [] \<longleftrightarrow> True\<close>
      | \<open>valid_index T (i#idx) \<longleftrightarrow> valid_index T idx \<and> valid_idx_step (index_type idx T) i\<close>

definition valid_rawaddr :: \<open>'TY rawaddr \<Rightarrow> bool\<close>
  where \<open>valid_rawaddr rawaddr \<longleftrightarrow> (
    case rawaddr of (addr, _) \<Rightarrow>
      Valid_Segment (memaddr.segment addr) \<and>
      valid_index (segidx.layout (memaddr.segment addr)) (memaddr.index addr))\<close>

definition valid_logaddr :: "'TY logaddr \<Rightarrow> bool"
  where "valid_logaddr addr \<longleftrightarrow>
    Valid_Segment (memaddr.segment addr) \<and>
    (memaddr.segment addr = Null \<longleftrightarrow> memaddr.index addr = []) \<and>
    valid_index (segidx.layout (memaddr.segment addr)) (memaddr.index addr)"

lemma valid_rawaddr_0[simp]: \<open>valid_rawaddr (0 |: [], 0)\<close>
  by (simp add: valid_rawaddr_def zero_prod_def Valid_Segment_def zero_memaddr_def zero_segidx_def)

lemma valid_logaddr_0[simp]: \<open>valid_logaddr (0 |: [])\<close>
  by (simp add: valid_logaddr_def zero_prod_def Valid_Segment_def zero_memaddr_def zero_segidx_def)

abbreviation memaddr_type :: \<open>'TY logaddr \<Rightarrow> 'TY\<close>
  where \<open>memaddr_type addr \<equiv> index_type (memaddr.index addr) (segidx.layout (memaddr.segment addr))\<close>


lemma MemObj_Size_LE_idx:
  \<open>valid_index T idx \<Longrightarrow> MemObj_Size (index_type idx T) \<le> MemObj_Size T\<close>
  by (induct idx arbitrary: T; simp)  (meson memobj_size_step le_trans)

lemma index_type_type_storable_in_mem:
  \<open>type_storable_in_mem T \<Longrightarrow> valid_index T idx \<Longrightarrow> type_storable_in_mem (index_type idx T)\<close>
  using MemObj_Size_LE_idx order.strict_trans1 by blast 

definition addr_raw_offset :: \<open>'TY \<Rightarrow> nat \<Rightarrow> size_t\<close>
  where \<open>addr_raw_offset T i = of_nat (idx_step_offset T i)\<close>

lemma addr_raw_offset_inj:
  \<open>type_storable_in_mem T
    \<Longrightarrow> valid_idx_step T i \<Longrightarrow> valid_idx_step T j
    \<Longrightarrow> addr_raw_offset T i = addr_raw_offset T j \<Longrightarrow> i = j\<close>
  by (simp add: addr_raw_offset_def word_of_nat_eq_iff Valid_Segment_def take_bit_nat_def)
     (metis idx_step_offset_inj idx_step_offset_step mod_less order_le_less_trans)

definition \<open>addr_abst_offset T ofst = (@i. valid_idx_step T i \<and> addr_raw_offset T i = ofst) \<close>

lemma addr_abst_raw_offset:
 \<open>type_storable_in_mem T
  \<Longrightarrow> valid_idx_step T i
  \<Longrightarrow> addr_abst_offset T (addr_raw_offset T i) = i\<close>
  unfolding addr_abst_offset_def using addr_raw_offset_inj by blast

definition logaddr_to_raw :: \<open>'TY logaddr \<Rightarrow> 'TY rawaddr\<close>
  where \<open>logaddr_to_raw addr =
    (case addr of seg |: (i#idx) \<Rightarrow> (seg |: idx, addr_raw_offset (index_type idx (segidx.layout seg)) i)
                | seg |: _ \<Rightarrow> (seg |: [], 0))\<close>

definition rawaddr_to_log :: \<open>'TY rawaddr \<Rightarrow> 'TY logaddr\<close>
  where \<open>rawaddr_to_log addr =
    (case addr of (seg |: idx, ofst) \<Rightarrow>
      if seg = Null then (Null |: [])
      else (seg |: (addr_abst_offset (index_type idx (segidx.layout seg)) ofst) # idx))\<close>

lemma logaddr_to_raw_segment[simp]:
  \<open>memaddr.segment (fst (logaddr_to_raw addr)) = memaddr.segment addr\<close>
  by (cases addr; case_tac x1; case_tac x2; simp add: logaddr_to_raw_def)

lemma logaddr_to_raw_0[simp]:
  \<open>logaddr_to_raw (0 |: []) = (0 |: [], 0)\<close>
  unfolding logaddr_to_raw_def by simp

lemma logaddr_to_raw_inj:
  \<open>valid_logaddr addr \<Longrightarrow> rawaddr_to_log (logaddr_to_raw addr) = addr\<close>
  by (cases addr, case_tac x2; case_tac x1;
      simp add: valid_logaddr_def logaddr_to_raw_def rawaddr_to_log_def
        addr_abst_raw_offset Valid_Segment_def index_type_type_storable_in_mem)

end


print_locale std_shared_val

locale std_sem =
  std_sem_pre where TYPES = TYPES
(* + std_shared_val where TYPE'TY = \<open>TYPE('TY)\<close> *)
  for TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N => 'VAL::nonsepable_semigroup) \<times> ('RES_N => 'RES::comm_monoid_mult)) itself\<close>
+ fixes Well_Type :: \<open>'TY \<Rightarrow> 'VAL set\<close>
    and Typeof :: \<open>'VAL \<Rightarrow> 'TY\<close>
  assumes WT_int[simp]: \<open>Well_Type (T_int.mk b)       = { V_int.mk (b,x) |b x. x < 2^b } \<close>
    and   WT_ptr[simp]: \<open>Well_Type (T_pointer.mk ())  = { V_pointer.mk addr    |addr. valid_rawaddr addr }\<close>
    and   WT_tup[simp]: \<open>Well_Type (T_tup.mk ts)      = { V_tup.mk vs          |vs. list_all2 (\<lambda> t v. v \<in> Well_Type t) ts vs }\<close>
    and   WT_arr[simp]: \<open>Well_Type (T_array.mk (t,n)) = { V_array.mk (t,vs)    |vs. length vs = n \<and> list_all (\<lambda>v. v \<in> Well_Type t) vs }\<close>
    and WT_Typeof[simp]: \<open>v \<in> Well_Type T \<Longrightarrow> Typeof v = T\<close>
    and Tyof_int[simp]: \<open>Typeof (V_int.mk (b,x)) = \<tau>Int b\<close>
    and Tyof_ptr[simp]: \<open>Typeof (V_pointer.mk rawaddr) = \<tau>Pointer\<close>
    and Tyof_tup[simp]: \<open>Typeof (V_tup.mk vs) = \<tau>Tuple (map Typeof vs)\<close>
    and Tyof_arr[simp]: \<open>Typeof (V_array.mk (t,vs)) = \<tau>Array (length vs) t\<close>

  fixes Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES set\<close>
  assumes res_valid_mem: \<open>Resource_Validator R_mem.name = R_mem.inject ` Valid_Mem\<close>
    and   res_valid_var: \<open>Resource_Validator R_var.name = UNIV\<close>

  fixes In_Mem :: \<open>('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'TY segidx \<Rightarrow> bool\<close>
  defines \<open>In_Mem res seg \<equiv> seg \<in> dom !!(R_mem.get res)\<close>

  fixes Can_EqCompare
  assumes can_eqcmp_ptr[simp]: "Can_EqCompare res (V_pointer.mk rp1) (V_pointer.mk rp2) \<longleftrightarrow>
              (memaddr.segment (fst rp1) = memaddr.segment (fst rp2)) \<or>
              (In_Mem res (memaddr.segment (fst rp1)) \<and> In_Mem res (memaddr.segment (fst rp2)))"
    and   can_eqcmp_int[simp]: "Can_EqCompare res (V_int.mk (b1,x1)) (V_int.mk (b2,x2)) \<longleftrightarrow> b1 = b2"
    and   can_eqcmp_sym: "Can_EqCompare res A B \<longleftrightarrow> Can_EqCompare res B A"
  fixes EqCompare
  assumes eqcmp_ptr[simp]: "EqCompare (V_pointer.mk rp1) (V_pointer.mk rp2) \<longleftrightarrow> rp1 = rp2"
    and   eqcmp_int[simp]: "EqCompare (V_int.mk i1) (V_int.mk i2) \<longleftrightarrow> i1 = i2"
(*  and   eqcmp_refl:  "EqCompare A A"
    and   eqcmp_sym:   "EqCompare A B \<longleftrightarrow> EqCompare B A"
    and   eqcmp_trans: "EqCompare A B \<Longrightarrow> EqCompare B C \<Longrightarrow> EqCompare A C" *)

  fixes Zero :: \<open>'TY \<Rightarrow> 'VAL\<close>
  assumes zero_well_typ: "Zero T \<in> Well_Type T"
    and   zero_int[simp]: \<open>Zero (T_int.mk b)      = V_int.mk (b,0)\<close>
    and   zero_ptr[simp]: \<open>Zero (T_pointer.mk ()) = V_pointer.mk 0\<close>
    and   zero_tup[simp]: \<open>Zero (T_tup.mk Ts)     = V_tup.mk (map Zero Ts)\<close>
    and   zero_arr[simp]: \<open>Zero (T_array.mk (T,N))= V_array.mk (T, replicate N (Zero T))\<close>

begin

definition "Valid_Resource = {R. (\<forall>N. R N \<in> Resource_Validator N)}"

paragraph \<open>Basic fictions for resource elements\<close>

definition "fiction_mem I = Fiction (\<lambda>x. { 1(R_mem #= y) |y. y \<in> \<I> I x})"
lemma fiction_mem_\<I>[simp]:
  "\<I> (fiction_mem I) = (\<lambda>x. { 1(R_mem #= y) |y. y \<in> \<I> I x})"
  unfolding fiction_mem_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def)

definition "fiction_var I = Fiction (\<lambda>x. { 1(R_var #= y) |y. y \<in> \<I> I x})"
lemma fiction_var_\<I>[simp]:
  "\<I> (fiction_var I) = (\<lambda>x. { 1(R_var #= y) |y. y \<in> \<I> I x})"
  unfolding fiction_var_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def)


definition "share_mem = fiction_mem (fiction.partialwise (
              fiction.pointwise (fiction.optionwise fiction.share)))"
definition "exclusive_var = fiction_var fiction.it"

end


subsubsection \<open>Pre-built Fiction\<close>

fiction_space (in std_sem) std_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> =
  mem :: share_mem
  var :: exclusive_var


subsubsection \<open>Standard Settings\<close>

type_synonym ('VAL,'RES_N,'RES) comp = \<open>'VAL opstack \<times> ('RES_N \<Rightarrow> 'RES)\<close>

locale std = std_fic
  where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup) \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult))\<close>
    and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
    and TYPE'REP = \<open>TYPE('FIC::comm_monoid_mult)\<close> 
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>
begin

abbreviation "INTERP_RES fic \<equiv> Valid_Resource \<inter> \<I> INTERP fic"

definition INTERP_COMP :: \<open>('VAL,'FIC_N,'FIC) comp set \<Rightarrow> ('VAL,'RES_N,'RES) comp set\<close>
  where "INTERP_COMP T = { (s,res) |s res fic. (s,fic) \<in> T \<and> res \<in> INTERP_RES fic }"


lemma INTERP_COMP[\<phi>expns]:
  \<open>(s,res) \<in> INTERP_COMP T \<longleftrightarrow> (\<exists>fic. (s,fic) \<in> T \<and> res \<in> INTERP_RES fic)\<close>
  unfolding INTERP_COMP_def by simp

definition "View_Shift u v \<longleftrightarrow> INTERP_RES u \<subseteq> INTERP_RES v "

end

(* type_synonym logaddr = "nat memaddr" *)


subsection \<open>Monadic Formalization\<close>

datatype ('VAL,'RES_N,'RES) state = Success (dest_state: "('VAL,'RES_N,'RES) comp") | Fail | PartialCorrect

text\<open> The basic state of the \<phi>-system virtual machine is represented by type "('a::lrep) state"}.
  The valid state `Success` essentially has two major form, one without registers and another one with them,
      \<^item> "StatOn (x1, x2, \<cdots>, xn, void)",
  where "(x1, x2, \<cdots>, xn, void)" represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term PartialCorrect} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term PartialCorrect} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>

declare state.split[split]

type_synonym ('VAL,'RES_N,'RES) proc = "('VAL,'RES_N,'RES) comp \<Rightarrow> ('VAL,'RES_N,'RES) state"


paragraph \<open>Elementary instructions\<close>

definition bind :: " ('VAL,'RES_N,'RES) state \<Rightarrow> ('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) state " \<comment>\<open>monadic bind\<close>
  where "bind s f = (case s of Success x \<Rightarrow> f x | Fail \<Rightarrow> Fail | PartialCorrect \<Rightarrow> PartialCorrect)"

definition instr_comp :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc"  ("_ \<then>/ _" [75,76] 75) 
  where "instr_comp f g s = bind (f s) g"

definition nop :: "('VAL,'RES_N,'RES) proc" where "nop = Success" \<comment>\<open>the instruction `no-operation`\<close>





section \<open>Specification Framework\<close>

type_synonym ('VAL,'RES_N,'RES) assn = "('VAL,'RES_N,'RES) comp set" \<comment> \<open>assertion\<close>

subsection \<open>Preliminary\<close>

subsubsection \<open>Predicates for Total Correctness & Partial Correctness\<close>

context std_sem begin

definition StrictStateTy :: "('VAL,'RES_N,'RES) comp set \<Rightarrow> ('VAL,'RES_N,'RES) state set" ("!\<S> _" [56] 55)
  where "!\<S> T = {s. case s of Success x \<Rightarrow> x \<in> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"
definition LooseStateTy :: "('VAL,'RES_N,'RES) comp set \<Rightarrow> ('VAL,'RES_N,'RES) state set" ("\<S> _" [56] 55)
  where "\<S> T = {s. case s of Success x \<Rightarrow> x \<in> T | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma StrictStateTy_expn[iff,\<phi>def]: "Success x \<in> !\<S> T \<equiv> x \<in> T"  "\<not> (Fail \<in> !\<S> T)"  "\<not> (PartialCorrect \<in> !\<S> T)"
  and LooseStateTy_expn[iff,\<phi>def]: "Success x \<in> \<S> T \<equiv> x \<in> T"  "\<not> (Fail \<in> \<S> T)"  "(PartialCorrect \<in> \<S> T)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
lemma LooseStateTy_expn' : "x \<in> \<S> T \<longleftrightarrow> x = PartialCorrect \<or> (\<exists>x'. x = Success x' \<and> x' \<in> T)"
  by (cases x) simp_all

lemma StrictStateTy_elim[elim]: "s \<in> !\<S> T \<Longrightarrow> (\<And>x. s = Success x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma StrictStateTy_intro[intro]: " x \<in> T \<Longrightarrow> Success x \<in> !\<S> T" by simp
lemma LooseStateTy_E[elim]:
  "s \<in> \<S> T \<Longrightarrow> (\<And>x. s = Success x \<Longrightarrow> x \<in> T \<Longrightarrow> C) \<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C) \<Longrightarrow> C" by (cases s) auto
lemma LooseStateTy_I[intro]:
  " x \<in> T \<Longrightarrow> Success x \<in> \<S> T" and [intro]: "PartialCorrect \<in> \<S> T" by simp_all
lemma LooseStateTy_upgrade: "s \<in> \<S> T \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T" by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> !\<S> T \<Longrightarrow> s \<in> \<S> T" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T) \<Longrightarrow> s \<in> \<S> T" by (cases s) auto

end


subsubsection \<open>Stack Element and Communicative Monoid Resource\<close>

consts Ele :: " 'a set \<Rightarrow> ('VAL,'FIC_N,'FIC) assn " ("ELE _" [17] 16)

context std begin

definition Val_Ele :: " 'VAL set \<Rightarrow> ('VAL,'FIC_N,'FIC) assn " ("VAL _" [17] 16)
  where "(VAL S) = { ([v], 1) | v. v \<in> S } "

adhoc_overloading Ele Val_Ele

lemma [\<phi>expns]:
  "(s,h) \<in> (VAL V) \<longleftrightarrow> h = 1 \<and> (\<exists>v. s = [v] \<and> v \<in> V)"
  unfolding Val_Ele_def by simp blast

lemma [elim!,\<phi>elim]:
  "Inhabited (VAL T) \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: pair_exists \<phi>expns)

definition Obj_Ele :: "('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('VAL,'FIC_N,'FIC) assn " ("OBJ _" [17] 16)
  where "(OBJ T) = { ([],h) | h. h \<in> T } "

adhoc_overloading Ele Obj_Ele

lemma [\<phi>expns]: "(s,h) \<in> (OBJ T) \<longleftrightarrow> s = [] \<and> h \<in> T"
  unfolding Obj_Ele_def by simp

lemma [elim!,\<phi>elim]: "Inhabited (OBJ T) \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: pair_exists \<phi>expns)

lemma OBJ_comm: \<open>S * (OBJ T) = (OBJ T) * S\<close>
  unfolding Obj_Ele_def times_set_def set_eq_iff apply simp
  using mult.commute by blast

end

(*
subsubsection \<open>Separation\<close>

definition disjoint :: " 'a set \<Rightarrow> 'a set \<Rightarrow> bool " (infixl "\<perpendicular>" 60) where "disjoint A B \<longleftrightarrow> (A \<inter> B = {})"
lemma disjoint_rewL: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> x \<notin> B)" unfolding disjoint_def by auto
lemma disjoint_rewR: "A \<perpendicular> B \<longleftrightarrow> (\<forall>x. x \<in> B \<longrightarrow> x \<notin> A)" unfolding disjoint_def by auto
lemma [elim]: "A \<perpendicular> B \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> False) \<Longrightarrow> C) \<Longrightarrow> C" unfolding disjoint_def by auto

lemma disjoint_empty [iff]: "{} \<perpendicular> S"  "S \<perpendicular> {}" unfolding disjoint_def by auto

context std begin

lemma Separation_expn:
  "(s,h) \<in> (T * U) \<longleftrightarrow> (\<exists>h1 h2 s1 s2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> s = s1 @\<^sub>s\<^sub>k s2 \<and> (h2,s2) \<in> T \<and> (h1,s1) \<in> U)"
  unfolding Separation_def by simp

lemma Separation_expn_R:
  "(h,s) \<in> (T * U) \<longleftrightarrow> (\<exists>h1 h2 s1 s2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> s = s1 @\<^sub>s\<^sub>k s2 \<and> (h1,s2) \<in> T \<and> (h2,s1) \<in> U)"
  unfolding Separation_def
  by simp (metis disjoint_def disjoint_rewR map_add_comm) 

lemma Separation_expn_V[nu_exps]:
  "(h, stack (deepize v # r)) \<in> (R * VAL V) \<longleftrightarrow> ((h, stack r) \<in> R \<and> v \<in> V )"
  unfolding Separation_def Shallowize'_expn
  by (simp add: nu_exps) force

end

lemma Separation_expn_V':
  "(h, s) \<in> (R * VAL V) \<longleftrightarrow> (\<exists>v r. s = stack (deepize v # r) \<and> (h, stack r) \<in> R \<and> v \<in> V )"
  unfolding Separation_def Shallowize'_expn
  by (simp add: nu_exps) force

lemma Separation_expn_O[nu_exps]:
  "(h,s) \<in> (R * OBJ H) \<longleftrightarrow>
  (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> (h2,s) \<in> Shallowize' R \<and> h1 \<in> H )"
  unfolding Separation_def Shallowize'_expn
  by (simp add: nu_exps)

lemma Separation_expn_O_R:
  "(h,s) \<in> (R * OBJ H) \<longleftrightarrow>
  (\<exists>h1 h2. h = h1 ++ h2 \<and> dom h1 \<perpendicular> dom h2 \<and> (h1,s) \<in> Shallowize' R \<and> h2 \<in> H )"
  unfolding Separation_def Shallowize'_expn
  by (simp add: nu_exps) (metis disjoint_def disjoint_rewR map_add_comm)

lemma [elim!,\<phi>elim]: "Inhabited (T * U) \<Longrightarrow> (Inhabited T \<Longrightarrow> Inhabited U \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: pair_exists nu_exps Separation_expn) blast


lemma Separation_assoc[simp]: "(A * (B * C)) = (A * B * C)"
  unfolding Separation_def set_eq_iff pair_forall
  apply auto subgoal for h2 s2 h1a h2a s1a s2a
    apply (rule exI [where x = "h1a"], rule exI [where x = "h2a ++ h2"],
          simp add: disjoint_def inf_sup_distrib1 inf_sup_distrib2)
    apply (rule exI [of _ s1a], rule exI [of _ "s2a @\<^sub>s\<^sub>k s2"], simp)
    apply blast done
  subgoal for h1 s1 h1a h2a s1a s2a
    apply (rule exI [where x = "h1 ++ h1a"], rule exI [where x = "h2a"],
          simp add: disjoint_def inf_sup_distrib1 inf_sup_distrib2)
    apply (rule exI [of _ "s1 @\<^sub>s\<^sub>k s1a"], simp, blast)
    done
  done

lemma Separation_comm:
  " (OBJ A * B) = (B * OBJ A) "
  " (A' * OBJ B') = (OBJ B' * A') "
  unfolding Separation_def set_eq_iff pair_forall
  by (simp_all add: disjoint_def nu_exps) (blast dest: map_add_comm)+

lemma shallowize_ex: "(\<exists>x::('c::lrep). P x) \<longleftrightarrow> (\<exists>x. P (shallowize x))"
  using deepize_inj by metis
lemma shallowize_ex': "TERM TYPE('c) \<Longrightarrow> (\<exists>x::('c::lrep). P x) \<longleftrightarrow> (\<exists>x. P (shallowize x))"
  using shallowize_ex .

lemma shallowize_all: "(\<forall>x::('c::lrep). P x) \<longleftrightarrow> (\<forall>x. P (shallowize x))"
  using deepize_inj by metis
lemma shallowize_all': "TERM TYPE('c) \<Longrightarrow> (\<forall>x::('c::lrep). P x) \<longleftrightarrow> (\<forall>x. P (shallowize x))"
  using shallowize_all .


lemma Separation_E[elim]:
  "(h,s) \<in> (T * U) \<Longrightarrow> (\<And>h1 h2 s1 s2. h = h1 ++ h2 \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> s = s1 @\<^sub>s\<^sub>k s2
      \<Longrightarrow> (h2,s2) \<in> T \<Longrightarrow> (h1,s1) \<in> U \<Longrightarrow> C) \<Longrightarrow> C "
  unfolding Separation_expn by simp blast

lemma Separation_I[intro]:
  "(h2,s2) \<in> T \<Longrightarrow> (h1,s1) \<in> U \<Longrightarrow> dom h1 \<perpendicular> dom h2 \<Longrightarrow> s = s1 @\<^sub>s\<^sub>k s2 \<Longrightarrow> (h1 ++ h2, s) \<in> (T * U)"
  unfolding Separation_expn by simp blast

*)

subsection \<open>Hoare Triple\<close>

definition (in std) \<phi>Procedure :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> bool"
    ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<rbrace>))" [101,2,2] 100)
  where [\<phi>def]:"\<phi>Procedure f T U \<longleftrightarrow>
    (\<forall>comp R. comp \<in> INTERP_COMP (R * T) \<longrightarrow> f comp \<in> \<S> INTERP_COMP (R * U))"


definition Map :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set " where "Map A B = {f. \<forall>a. a \<in> A \<longrightarrow> f a \<in> B }"
definition Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<lbrace>(2 _/ \<longmapsto> _ )\<rbrace>)" [101,2,2] 100)
  where [\<phi>def]: "\<^bold>m\<^bold>a\<^bold>p f \<lbrace> T \<longmapsto> U \<rbrace> \<equiv> \<forall>a. a \<in> T \<longrightarrow> f a \<in> U"


paragraph \<open>Specifications for Elementary Monadic Construction\<close>

lemma (in std) nop_\<phi>app: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c nop \<lbrace> T \<longmapsto> T \<rbrace>" unfolding nop_def \<phi>Procedure_def by auto

lemma (in std) instr_comp[intro]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> B \<longmapsto> C \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<then> g) \<lbrace> A \<longmapsto> C \<rbrace>"
  unfolding instr_comp_def \<phi>Procedure_def bind_def by (auto 0 4)


section \<open>Programming Framework\<close>

subsection \<open>Base\<close>

definition CodeBlock :: "('VAL,'RES_N,'RES) state \<Rightarrow> ('VAL,'RES_N,'RES) state => ('VAL,'RES_N,'RES) proc \<Rightarrow> bool"
  where "CodeBlock stat arg prog \<longleftrightarrow> (bind arg prog = stat \<and> stat \<noteq> PartialCorrect)"

(* syntax "_codeblock_exp_" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> bool"  ("(2\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _/  \<^bold>a\<^bold>s '\<open>_'\<close>/ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>)" [100,0,0] 3)
syntax "_codeblock_" :: "idt \<Rightarrow> logic \<Rightarrow> bool" ("\<^bold>c\<^bold>o\<^bold>d\<^bold>e\<^bold>b\<^bold>l\<^bold>o\<^bold>c\<^bold>k _ \<^bold>f\<^bold>o\<^bold>r \<^bold>a\<^bold>r\<^bold>g\<^bold>u\<^bold>m\<^bold>e\<^bold>n\<^bold>t\<^bold>s '\<open>_'\<close>" [100,0] 3) *)

definition (in std)
  CurrentConstruction :: " ('VAL,'RES_N,'RES) state \<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> bool "
    ("\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t _ [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,11] 10)
  where "CurrentConstruction s R S \<longleftrightarrow> s \<in> !\<S> INTERP_COMP (R * S)"

definition (in std)
  PendingConstruction :: " ('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) state \<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> ('VAL,'FIC_N,'FIC) assn \<Rightarrow> bool "
    ("\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g _ \<^bold>o\<^bold>n _ [_] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n/ _" [1000,1000,1000,5] 4)
    where "PendingConstruction f s R S \<longleftrightarrow> bind s f \<in> \<S> INTERP_COMP (R * S)"

lemma (in std) CurrentConstruction_D: "CurrentConstruction s H T \<Longrightarrow> Inhabited T"
  unfolding CurrentConstruction_def Inhabited_def by (cases s) (auto 0 4 simp add: \<phi>expns)


paragraph \<open>Rules for Constructing Programs\<close>

context std begin

lemma \<phi>frame:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> M * A \<longmapsto> M * B \<rbrace>"
  unfolding \<phi>Procedure_def
  by (metis (no_types, lifting) mult.assoc)

lemma \<phi>apply_proc:
  "(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> S \<longmapsto> T \<rbrace> \<Longrightarrow> (\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T)"
  unfolding \<phi>Procedure_def CurrentConstruction_def PendingConstruction_def bind_def by (auto 0 5)

lemma \<phi>accept_proc:
  "\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> CodeBlock s' s f \<Longrightarrow> \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s' [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def
  by (simp add: LooseStateTy_upgrade)

lemma \<phi>reassemble_proc_0:
  "\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g nop \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def nop_def bind_def by (cases s) simp+

lemma \<phi>reassemble_proc:
  "(\<And>s'. CodeBlock s' s f \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s' [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g (f \<then> g) \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T"
  unfolding CurrentConstruction_def PendingConstruction_def CodeBlock_def bind_def instr_comp_def
  by force

lemma \<phi>reassemble_proc_final:
  "(\<And>s H. \<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n S \<Longrightarrow> \<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g g \<^bold>o\<^bold>n s [H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c g \<lbrace> S \<longmapsto> T \<rbrace>"
  unfolding CurrentConstruction_def PendingConstruction_def \<phi>Procedure_def bind_def pair_All
  by (metis StrictStateTy_intro state.simps(8))

lemma \<phi>rename_proc: "f \<equiv> f' \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f' \<lbrace> U \<longmapsto> \<R> \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> U \<longmapsto> \<R> \<rbrace>" by fast

end




section \<open>\<phi>-Type\<close>

type_synonym ('concrete,'abstract) \<phi> = " 'abstract \<Rightarrow> 'concrete set "

subsubsection \<open>Definitions\<close>

definition \<phi>Type :: "'b \<Rightarrow> ('a,'b) \<phi> \<Rightarrow> 'a set" (infix "\<Ztypecolon>" 17) where " (x \<Ztypecolon> T) = (T x)"

lemma typing_inhabited: "p \<in> (x \<Ztypecolon> T) \<Longrightarrow> Inhabited (x \<Ztypecolon> T)"
  unfolding Inhabited_def \<phi>Type_def by blast


paragraph \<open>Syntax\<close>

abbreviation (in std) COMMA
  :: \<open>('VAL,'FIC_N,'FIC) comp set \<Rightarrow> ('VAL,'FIC_N,'FIC) comp set \<Rightarrow> ('VAL,'FIC_N,'FIC) comp set\<close> (infixl "\<heavy_comma>" 15)
  where \<open>COMMA \<equiv> (*)\<close>

translations
  "CONST std.COMMA S (y \<Ztypecolon> T)" \<rightleftharpoons> "CONST std.COMMA S (ELE y \<Ztypecolon> T)"
  "CONST std.COMMA (x \<Ztypecolon> T) S" \<rightleftharpoons> "CONST std.COMMA (ELE x \<Ztypecolon> T) S"
  "CONST std.\<phi>Procedure RV I f (a \<Ztypecolon> A) B" \<rightleftharpoons> "CONST std.\<phi>Procedure RV I f (ELE a \<Ztypecolon> A) B"
  "CONST std.\<phi>Procedure RV I f A (b \<Ztypecolon> B)" \<rightleftharpoons> "CONST std.\<phi>Procedure RV I f A (ELE b \<Ztypecolon> B)"
  "CONST std.CurrentConstruction RV I s R (x \<Ztypecolon> T)" \<rightleftharpoons> "CONST std.CurrentConstruction RV I s R (ELE (x \<Ztypecolon> T))"
  "CONST std.PendingConstruction RV I f s H (x \<Ztypecolon> T)" \<rightleftharpoons> "CONST std.PendingConstruction RV I f s H (ELE x \<Ztypecolon> T)"


subsubsection \<open>Properties\<close>

context std_sem begin

definition \<phi>Zero :: "'TY \<Rightarrow> ('VAL,'a) \<phi> \<Rightarrow> 'a \<Rightarrow> bool"
  where [\<phi>def]: "\<phi>Zero ty T x \<longleftrightarrow> Zero ty \<in> (x \<Ztypecolon> T)"

definition \<phi>Equal :: "('VAL,'a) \<phi> \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where [\<phi>def]: "\<phi>Equal T can_eq eq \<longleftrightarrow> (\<forall>p1 p2 x1 x2 res.
    can_eq x1 x2 \<and> p1 \<in> (x1 \<Ztypecolon> T) \<and> p2 \<in> (x2 \<Ztypecolon> T)
      \<longrightarrow> Can_EqCompare res p1 p2 \<and> (EqCompare p1 p2 = eq x1 x2))"

end



end
