(* KEEP IT SIMPLE AND STUPID *)

theory NuPrime \<comment> \<open>The Primary Theory of the \<phi>-System\<close>
  imports Main
    "HOL-Library.Word"
    NoePreliminary
    "HOL-Library.Adhoc_Overloading"
    Fictional_Algebra
    "Virt_Datatype/Virtual_Datatype"
  abbrevs "<:>" = "\<Ztypecolon>"
    and "<throws>" = "\<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s"
begin

chapter \<open>Semantics & Specification Framework --- Base of the Programming Language\<close>

section \<open>Semantic Framework\<close>

subsection \<open>Semantic Models\<close>

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

definition \<open>length_\<tau>Array T = (@N. \<exists>any. T = \<tau>Array N any)\<close>
abbreviation \<open>is_\<tau>Array T t \<equiv> (\<exists>N. t = \<tau>Array N T)\<close>

lemma length_\<tau>Array[simp]:
  \<open>length_\<tau>Array (\<tau>Array N T) = N\<close>
  unfolding length_\<tau>Array_def
  by blast

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
abbreviation to_size_t :: \<open>nat \<Rightarrow> size_t\<close> where \<open>to_size_t \<equiv> of_nat\<close>


datatype ('TY) segidx = Null | Segment nat \<comment> \<open>nonce\<close> (layout: 'TY)
declare segidx.map_id0[simp]

hide_const (open) layout

datatype ('index,'TY) memaddr = memaddr (segment: "'TY segidx") (index: 'index ) (infixl "|:" 60)
declare memaddr.sel[iff]
hide_const (open) segment index

type_synonym 'TY logaddr = "(nat list, 'TY) memaddr" (* the index of logaddr is non empty *)
type_synonym 'TY rawaddr = \<open>(size_t, 'TY) memaddr\<close>

instantiation segidx :: (type) zero begin
definition [simp]: "zero_segidx = Null"
instance ..
end

instantiation memaddr :: (zero, type) zero begin
definition "zero_memaddr = (0 |: 0)"
instance ..
end


lemma infinite_UNIV_int [simp]: "\<not> finite (UNIV::int set)"
proof
  assume "finite (UNIV::int set)"
  moreover have "inj (\<lambda>i::int. 2 * i)"
    by (rule injI) simp
  ultimately have "surj (\<lambda>i::int. 2 * i)"
    by (rule finite_UNIV_inj_surj)
  thm finite_UNIV_inj_surj
  then obtain i :: int where "1 = 2 * i" by (rule surjE)
  then show False by (simp add: pos_zmult_eq_1_iff)
qed

lemma segidx_infinite[simp]:
  \<open>infinite (UNIV :: 'a segidx set)\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>(UNIV :: 'a segidx set)\<close>
        and f = \<open>\<lambda>n. Segment n undefined\<close>]
  by (meson infinite_UNIV_char_0 injI segidx.inject top_greatest)

lemma segidx_infinite_TY:
  \<open>infinite {a. segidx.layout a = TY}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{a. segidx.layout a = TY}\<close>
        and f = \<open>\<lambda>n. Segment n TY\<close>]
  using inj_def by fastforce


abbreviation shift_addr :: "('idx,'TY) memaddr \<Rightarrow> ('idx::monoid_add) \<Rightarrow> ('idx,'TY) memaddr" (infixl "||+" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. x + delta) id addr"

lemma mem_shift_shift[simp]: "a ||+ i ||+ j = a ||+ (i + j)" by (cases a) (simp add: add.assoc)

lemma memaddr_segment_shift[simp]:
  \<open>memaddr.segment (a ||+ i) = memaddr.segment a\<close>
  by (cases a, simp)

lemma memaddr_index_shift[simp]:
  \<open>memaddr.index (a ||+ i) = memaddr.index a + i\<close>
  by (cases a, simp)

lemma mem_shift_add_cancel[simp]:
  \<open>(a ||+ i) = (a ||+ j) \<longleftrightarrow> i = j\<close>
  for i :: \<open>'a::{monoid_add,cancel_semigroup_add}\<close>
  by (cases a, simp)



paragraph \<open>Model\<close>

virtual_datatype 'TY std_val :: "nonsepable_semigroup" =
  V_int     :: \<open>nat \<times> nat\<close>
  V_pointer :: \<open>'TY rawaddr\<close>
  V_tup     :: \<open>'self list\<close>
  V_array   :: \<open>'TY \<times> 'self list\<close>

(*virtual_datatype 'TY std_shared_val :: sep_algebra =
  SV_int     :: \<open>nat \<times> nat share option\<close>
  SV_pointer :: \<open>'TY rawaddr share option\<close>
  SV_tup     :: \<open>'self list\<close>
  SV_array   :: \<open>'TY \<times> 'self list\<close>
*)

subsubsection \<open>Resource\<close>

type_synonym 'v opstack = "'v list"
typedef varname = \<open>UNIV::nat set\<close> ..
type_synonym ('TY,'VAL) R_mem' = \<open>('TY segidx \<rightharpoonup> 'VAL)\<close>
type_synonym ('TY,'VAL) R_mem = \<open>('TY,'VAL) R_mem' ?\<close>
type_synonym ('TY,'VAL) R_var = \<open>(varname \<rightharpoonup> 'VAL) ?\<close>

lemma infinite_varname:
  \<open>infinite (UNIV::varname set)\<close>
  by (metis (mono_tags, opaque_lifting) Rep_varname_cases UNIV_I finite_imageI infinite_UNIV_char_0 surj_def)

resource_space ('VAL::"nonsepable_semigroup",'TY) std_res =
  R_mem :: \<open>('TY,'VAL) R_mem\<close>
  R_var :: \<open>('TY,'VAL) R_var\<close>

paragraph \<open>Valid Memory\<close>

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

fixes Well_Type :: \<open>'TY \<Rightarrow> 'VAL set\<close>
assumes Well_Type_disjoint: \<open>ta \<noteq> tb \<Longrightarrow> Well_Type ta \<inter> Well_Type tb = {}\<close>

assumes V_tup_mult: \<open>V_tup.mk t1 * V_tup.mk t2 = V_tup.mk (t1 @ t2)\<close>
  fixes MemObj_Size :: \<open>'TY \<Rightarrow> nat\<close> \<comment> \<open>in size of bytes\<close>
    and valid_idx_step :: \<open>'TY \<Rightarrow> nat \<Rightarrow> bool\<close>
    and idx_step_type   :: \<open>nat \<Rightarrow> 'TY \<Rightarrow> 'TY\<close>
    and idx_step_value  :: \<open>nat \<Rightarrow> 'VAL \<Rightarrow> 'VAL\<close>
    and idx_step_mod_value :: \<open>nat \<Rightarrow> ('VAL \<Rightarrow> 'VAL) \<Rightarrow> 'VAL \<Rightarrow> 'VAL\<close>
    and idx_step_offset :: \<open>'TY \<Rightarrow> nat \<Rightarrow> nat\<close>
    and type_measure :: \<open>'TY \<Rightarrow> nat\<close>
(*  assumes MemObj_Size_L0[simp]: \<open>0 < MemObj_Size x\<close>
     *)
  assumes memobj_size_arr    : \<open>MemObj_Size (\<tau>Array N T) = N * MemObj_Size T\<close>
    and   memobj_size_step   : \<open>valid_idx_step T i \<Longrightarrow> MemObj_Size (idx_step_type i T) \<le> MemObj_Size T\<close>
    and   idx_step_type_measure: \<open>valid_idx_step T i \<Longrightarrow> type_measure (idx_step_type i T) < type_measure T\<close>
    and   idx_step_type_tup  : \<open>i < length tys \<Longrightarrow> idx_step_type i (\<tau>Tuple tys) = tys!i \<close>
    and   idx_step_type_arr  : \<open>i \<le> N \<Longrightarrow> idx_step_type i (\<tau>Array N T) = T\<close>
    and   valid_idx_step_tup : \<open>valid_idx_step (\<tau>Tuple tys) i \<longleftrightarrow> i < length tys\<close>
    and   valid_idx_step_arr : \<open>valid_idx_step (\<tau>Array N T) i \<longleftrightarrow> i < N\<close>
    and   idx_step_value_welltyp: \<open>valid_idx_step T i \<Longrightarrow> v \<in> Well_Type T \<Longrightarrow> idx_step_value i v \<in> Well_Type (idx_step_type i T)\<close>
    and   idx_step_value_tup : \<open>idx_step_value i (V_tup.mk vs)   = vs!i\<close>
    and   idx_step_value_arr : \<open>idx_step_value i (V_array.mk (T,vs)) = vs!i\<close>
    and   idx_step_mod_value : \<open>valid_idx_step T i
                            \<Longrightarrow> valid_idx_step T j
                            \<Longrightarrow> v \<in> Well_Type T
                            \<Longrightarrow> idx_step_value i (idx_step_mod_value j f v) =
                                  (if i = j then f (idx_step_value j v) else idx_step_value i v) \<close>
    and   idx_step_mod_value_welltyp: \<open>valid_idx_step T i
                                   \<Longrightarrow> v \<in> Well_Type T
                                   \<Longrightarrow> f (idx_step_value i v) \<in> Well_Type (idx_step_type i T)
                                   \<Longrightarrow> idx_step_mod_value i f v \<in> Well_Type T\<close>
    and   idx_step_mod_value_tup : \<open>idx_step_mod_value i f (V_tup.mk vs) = V_tup.mk (vs[i := f (vs!i)])\<close>
    and   idx_step_mod_value_arr : \<open>idx_step_mod_value i f (V_array.mk (T,vs)) = V_array.mk (T,vs[i := f (vs!i)])\<close>
    and   idx_step_offset_arr: \<open>idx_step_offset (\<tau>Array N T) i = i * MemObj_Size T\<close>
    and   idx_step_offset_size:\<open>valid_idx_step T i \<Longrightarrow> idx_step_offset T i + MemObj_Size (idx_step_type i T) \<le> MemObj_Size T\<close>
    and   idx_step_offset_disj:\<open>valid_idx_step T i \<Longrightarrow> valid_idx_step T j \<Longrightarrow>
                                idx_step_offset T i \<le> idx_step_offset T j \<Longrightarrow>
                                idx_step_offset T j < idx_step_offset T i + MemObj_Size (idx_step_type i T) \<Longrightarrow>
                                i = j\<close>
    
      \<comment> \<open>It may introduce a restriction: types like zero-element tuple and array must occupy at
          least 1 byte, which may affect the performance unnecessarily. However, since zero-element
          tuple and array are so special ...One thing: we do not support arbitrary-length array like [0 x nat] in LLVM? TODO \<close>
begin

lemma V_tup_mult_cons:
  \<open>NO_MATCH vs ([]::'VAL list) \<Longrightarrow> V_tup.mk (v#vs) = V_tup.mk [v] * V_tup.mk vs\<close>
  using V_tup_mult by simp

lemma Well_Type_unique:
  \<open>v \<in> Well_Type ta \<Longrightarrow> v \<in> Well_Type tb \<Longrightarrow> ta = tb\<close>
  using Well_Type_disjoint by blast

abbreviation \<open>type_storable_in_mem T \<equiv> MemObj_Size T < 2^addrspace_bits\<close>

definition \<open>Valid_Segment seg = (
    case seg of Null \<Rightarrow> True
              | Segment _ ty \<Rightarrow> type_storable_in_mem ty
    )\<close>

lemma Valid_Segment_zero[simp]: \<open>Valid_Segment Null\<close>
  unfolding Valid_Segment_def zero_segidx_def by simp

definition Valid_Mem :: "('TY,'VAL) R_mem set"
  where "Valid_Mem = { Fine h |h. finite (dom h)
                                \<and> (\<forall>seg \<in> dom h. h seg \<in> Some ` Well_Type (segidx.layout seg))}"

lemma Valid_Mem_1[simp]: \<open>1 \<in> Valid_Mem\<close>
  unfolding Valid_Mem_def one_fun_def one_fine_def by simp

lemma Mem_freshness:
  \<open>finite (dom f) \<Longrightarrow> \<exists>k. f k = None \<and> segidx.layout k = TY\<close>
  unfolding dom_def
  by (smt (verit, del_insts) Collect_mono finite_Collect_disjI finite_subset segidx_infinite_TY)
  

abbreviation \<open>index_value \<equiv> fold idx_step_value\<close>
abbreviation \<open>index_type  \<equiv> fold idx_step_type\<close>
abbreviation \<open>index_mod_value \<equiv> foldr idx_step_mod_value\<close>

primrec valid_index :: \<open>'TY \<Rightarrow> nat list \<Rightarrow> bool\<close>
  where \<open>valid_index T [] \<longleftrightarrow> True\<close>
      | \<open>valid_index T (i#idx) \<longleftrightarrow> valid_idx_step T i \<and> valid_index (idx_step_type i T) idx\<close>

lemma valid_index_tail[simp]:
  \<open>valid_index T (idx@[i]) \<longleftrightarrow> valid_index T idx \<and> valid_idx_step (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma index_type_measure:
  \<open>valid_index T idx \<Longrightarrow> idx \<noteq> [] \<Longrightarrow> type_measure (index_type idx T) < type_measure T\<close>
  apply (induct idx arbitrary: T; simp)
  by (metis dual_order.strict_trans fold_simps(1) idx_step_type_measure)

lemma valid_index_cat: \<open>valid_index T (a@b) \<Longrightarrow> valid_index T a \<and> valid_index (index_type a T) b\<close>
  by (induct a arbitrary: T; simp)

lemma valid_index_cons: \<open>valid_index T [i] \<longleftrightarrow> valid_idx_step T i\<close> by simp

lemma index_value_welltyp:
  \<open>valid_index T idx \<Longrightarrow> v \<in> Well_Type T \<Longrightarrow> index_value idx v \<in> Well_Type (index_type idx T)\<close>
  apply (induct idx arbitrary: v T; simp)
  using idx_step_value_welltyp
  by blast

lemma index_mod_value_welltyp:
   \<open>valid_index T idx
\<Longrightarrow> v \<in> Well_Type T
\<Longrightarrow> f (index_value idx v) \<in> Well_Type (index_type idx T)
\<Longrightarrow> index_mod_value idx f v \<in> Well_Type T\<close>
  apply (induct idx arbitrary: T v; simp)
  using idx_step_mod_value_welltyp idx_step_value_welltyp by blast



primrec index_offset :: \<open>'TY \<Rightarrow> nat list \<Rightarrow> nat\<close>
  where \<open>index_offset T [] = 0\<close>
      | \<open>index_offset T (i#idx) = idx_step_offset T i + index_offset (idx_step_type i T) idx\<close>

lemma index_offset_tail[simp]:
  \<open>index_offset T (idx@[i]) = index_offset T idx + idx_step_offset (index_type idx T) i\<close>
  by (induct idx arbitrary: T; simp)

lemma index_offset_upper_bound:
  \<open>valid_index T (base@idx) \<Longrightarrow>
   index_offset T (base@idx) + MemObj_Size (index_type (base@idx) T) \<le> index_offset T base + MemObj_Size (index_type base T)\<close>
  apply (induct idx arbitrary: base rule: rev_induct;
         simp del: append_assoc add: append_assoc[symmetric] fold_tail)
  using idx_step_offset_size by fastforce

lemmas index_offset_upper_bound_0 = index_offset_upper_bound[where base = "[]", simplified]

lemma index_offset_bound:
  \<open>valid_index T (base@idx) \<Longrightarrow>
  index_offset T base \<le> index_offset T (base@idx) \<and> index_offset T (base@idx) \<le> index_offset T base + MemObj_Size (index_type base T)\<close>
  apply (induct idx arbitrary: base rule: rev_induct;
         simp del: append_assoc add: append_assoc[symmetric] fold_tail)
  using idx_step_offset_size index_offset_upper_bound by fastforce

lemma index_offset_bound_strict:
  \<open>valid_index T (base@idx) \<Longrightarrow> 0 < MemObj_Size (index_type (base@idx) T) \<Longrightarrow>
  index_offset T base \<le> index_offset T (base@idx) \<and> index_offset T (base@idx) < index_offset T base + MemObj_Size (index_type base T)\<close>
  apply (induct idx arbitrary: base rule: rev_induct;
         simp del: append_assoc add: append_assoc[symmetric] fold_tail)
  using idx_step_offset_size index_offset_upper_bound by fastforce

lemma index_type_idem:
  \<open>valid_index T idx \<Longrightarrow> index_type idx T = T \<longleftrightarrow> idx = []\<close>
  apply (cases idx; simp; rule)
  using index_type_measure
  by (metis fold_simps(2) list.discI order_less_irrefl valid_index.simps(2))





paragraph \<open>Address & Pointer\<close>

abbreviation valid_rawaddr :: \<open>'TY rawaddr \<Rightarrow> bool\<close>
  where \<open>valid_rawaddr addr \<equiv> Valid_Segment (memaddr.segment addr)\<close>

definition valid_logaddr :: "'TY logaddr \<Rightarrow> bool"
  where "valid_logaddr addr \<longleftrightarrow>
    Valid_Segment (memaddr.segment addr) \<and>
    (memaddr.segment addr = Null \<longrightarrow> memaddr.index addr = []) \<and>
    valid_index (segidx.layout (memaddr.segment addr)) (memaddr.index addr)"

lemma valid_rawaddr_0[simp]: \<open>valid_rawaddr (0 |: 0)\<close>
  by (simp add: zero_prod_def Valid_Segment_def zero_memaddr_def zero_segidx_def)

lemma valid_logaddr_0[simp]: \<open>valid_logaddr (0 |: [])\<close>
  by (simp add: valid_logaddr_def zero_prod_def Valid_Segment_def zero_memaddr_def zero_segidx_def)

abbreviation logaddr_type :: \<open>'TY logaddr \<Rightarrow> 'TY\<close>
  where \<open>logaddr_type addr \<equiv> index_type (memaddr.index addr) (segidx.layout (memaddr.segment addr))\<close>

lemma MemObj_Size_LE_idx:
  \<open>valid_index T (base@idx) \<Longrightarrow> MemObj_Size (index_type (base@idx) T) \<le> MemObj_Size (index_type base T)\<close>
  apply (induct base arbitrary: T idx; simp)
  subgoal for T idx apply (induct idx arbitrary: T; simp)
    using memobj_size_step order.trans by blast
  done

lemmas MemObj_Size_LE_idx_0 = MemObj_Size_LE_idx[where base = "[]", simplified]

lemma index_type_type_storable_in_mem:
  \<open>type_storable_in_mem T \<Longrightarrow> valid_index T idx \<Longrightarrow> type_storable_in_mem (index_type idx T)\<close>
  using MemObj_Size_LE_idx_0 order.strict_trans1 by blast 

lemma logaddr_storable_in_mem:
  \<open>valid_logaddr addr \<Longrightarrow> addr \<noteq> 0 \<Longrightarrow> type_storable_in_mem (logaddr_type addr)\<close>
  unfolding valid_logaddr_def Valid_Segment_def zero_memaddr_def
  apply (cases addr; simp)
  subgoal for seg idx by (cases seg; simp add: index_type_type_storable_in_mem)
  done

definition logaddr_to_raw :: \<open>'TY logaddr \<Rightarrow> 'TY rawaddr\<close>
  where \<open>logaddr_to_raw addr =
    (case addr of seg |: idx \<Rightarrow> seg |: to_size_t (index_offset (segidx.layout seg) idx))\<close>

lemma logaddr_to_raw_0[simp]:
  \<open>logaddr_to_raw (0 |: []) = (0 |: 0)\<close>
  unfolding logaddr_to_raw_def by simp

lemma logaddr_to_raw_segment[simp]:
  \<open>memaddr.segment (logaddr_to_raw addr) = memaddr.segment addr\<close>
  unfolding logaddr_to_raw_def by (cases addr) simp

lemma valid_logaddr_rawaddr [simp]:
  \<open>valid_logaddr addr \<Longrightarrow> valid_rawaddr (logaddr_to_raw addr)\<close>
  unfolding valid_logaddr_def by simp 


lemma
  assumes prems:
    \<open>valid_index T index1\<close>
    \<open>valid_index T index2\<close>
    \<open>index_type index2 T = index_type index1 T\<close>
    \<open>0 < MemObj_Size (index_type index1 T)\<close>
  shows index_offset_inj:
    \<open>index_offset T index1 = index_offset T index2 \<longrightarrow> index1 = index2\<close>
proof -
  consider (either_nil) \<open>index1 = [] \<or> index2 = []\<close>
      |   (both_notnil) \<open>index1 \<noteq> [] \<and> index2 \<noteq> []\<close>
      by blast
  then show ?thesis
  proof cases
    case either_nil
      then show ?thesis using prems index_type_idem by metis
  next
    case both_notnil
    have \<open>index1 \<noteq> index2 \<longrightarrow> index_offset T index1 \<noteq> index_offset T index2\<close> (is \<open>?neq \<longrightarrow> ?goal\<close>)
    proof
      assume neq: ?neq

      have t1: \<open>\<And>idx1 idx2. idx1 \<noteq> [] \<and> idx2 \<noteq> [] \<and> idx1 \<noteq> idx2 \<and> \<not>(\<exists>d. idx1@d = idx2) \<and> \<not>(\<exists>d. idx2@d = idx1)
          \<Longrightarrow> \<exists>i. i < length idx1 \<and> i < length idx2 \<and> idx1 ! i \<noteq> idx2 ! i \<close>
        unfolding list_eq_iff_nth_eq nth_append apply simp apply clarify
        subgoal premises prems for idx1 idx2
          apply (cases \<open>length idx1 \<le> length idx2\<close>)
          using prems(4)[THEN spec[where x=\<open>drop (length idx1) idx2\<close>], simplified]
           apply (metis le_add_diff_inverse linordered_semidom_class.add_diff_inverse nth_drop)
          using prems(5)[THEN spec[where x=\<open>drop (length idx2) idx1\<close>], simplified]
           by (metis add_diff_inverse_nat le_add_diff_inverse nat_le_linear nth_drop)
         done

       moreover have t2: \<open>\<And>i idx1 idx2. i < length idx1 \<and> i < length idx2 \<and> idx1 ! i \<noteq> idx2 ! i
          \<Longrightarrow> \<exists>i. i < length idx1 \<and> i < length idx2 \<and> idx1 ! i \<noteq> idx2 ! i \<and> take i idx1 = take i idx2\<close>
         unfolding list_eq_iff_nth_eq apply simp
         subgoal for i idx1 idx2
           apply (induct i arbitrary: idx1 idx2 rule: nat_less_induct)
           by (smt (verit, ccfv_threshold) min.absorb4 min_less_iff_conj)
         done

       ultimately have t3:
          \<open>\<And>idx1 idx2. idx1 \<noteq> [] \<and> idx2 \<noteq> [] \<and> idx1 \<noteq> idx2 \<and> \<not>(\<exists>d. idx1@d = idx2) \<and> \<not>(\<exists>d. idx2@d = idx1)
          \<Longrightarrow> \<exists>i. i < length idx1 \<and> i < length idx2 \<and> idx1 ! i \<noteq> idx2 ! i \<and> take i idx1 = take i idx2\<close>
         by (smt (verit, ccfv_threshold))

       note t4 = t3[of \<open>index1\<close> \<open>index2\<close>, simplified both_notnil, simplified]
         

       have \<open>\<not>((\<exists>d. index1@d = index2) \<or> (\<exists>d. index2@d = index1))\<close>
       proof
         assume A: \<open>(\<exists>d. index1 @ d = index2) \<or> (\<exists>d. index2 @ d = index1)\<close>
         then consider (L) \<open>\<exists>d. index1 @ d = index2\<close> |
                       (R) \<open>(\<exists>d. index2 @ d = index1)\<close> by blast
         then show False
         proof cases
           case L
           then obtain d where D: \<open>index2 = index1@d\<close> by blast
           then have \<open>valid_index (index_type index1 T) d\<close> using valid_index_cat prems by blast
           then have \<open>d = []\<close> using fold_append prems D by (simp add: index_type_idem)
           then show False using neq D by blast
         next
           case R
           then obtain d where D: \<open>index1 = index2@d\<close> by blast
           then have \<open>valid_index (index_type index2 T) d\<close> using valid_index_cat prems by blast
           then have \<open>d = []\<close> using fold_append prems D by (metis comp_def index_type_idem) 
           then show False using neq D by blast
         qed
       qed
      then have \<open>\<exists>base i1 idx1 i2 idx2. index1 = (base@[i1])@idx1 \<and> index2 = (base@[i2])@idx2 \<and> i1 \<noteq> i2\<close>
        using neq both_notnil t4
        by (metis append.assoc append_Cons append_Nil id_take_nth_drop)
      then obtain base i1 idx1 i2 idx2 where
        obt: \<open>(base@[i1])@idx1 = index1 \<and> (base@[i2])@idx2 = index2 \<and> i1 \<noteq> i2\<close>
        by blast

      have valid_idx_step_i1: \<open>valid_idx_step (index_type base T) i1\<close>
        using prems valid_index_cat valid_index_cons obt by blast
      have valid_idx_step_i2: \<open>valid_idx_step (index_type base T) i2\<close>
        using prems valid_index_cat valid_index_cons obt by blast
      have \<open>index_offset T index1 \<noteq> index_offset T index2\<close>
        using index_offset_bound_strict[where base = \<open>base@[i1]\<close> and idx = idx1 and T = T,
                                        simplified index_offset_tail obt prems fold_tail]
              index_offset_bound_strict[where base = \<open>base@[i2]\<close> and idx = idx2 and T = T,
                                        simplified index_offset_tail obt prems fold_tail]
              idx_step_offset_disj[where T = \<open>index_type base T\<close> and i = i1 and j = i2]
        by (smt (verit, ccfv_SIG) comp_def group_cancel.add1 idx_step_offset_disj nat_add_left_cancel_less nat_le_linear obt order.strict_trans1 valid_idx_step_i1 valid_idx_step_i2)
      then show ?goal
        using obt prems by presburger
    qed
    then show ?thesis using prems by blast
    qed
  qed

lemma logaddr_to_raw_inj:
    \<open>valid_logaddr addr1 \<Longrightarrow>
     valid_logaddr addr2 \<Longrightarrow>
     logaddr_type addr1 = logaddr_type addr2 \<Longrightarrow>
     0 < MemObj_Size (logaddr_type addr1) \<Longrightarrow>
     logaddr_to_raw addr1 = logaddr_to_raw addr2 \<longrightarrow> addr1 = addr2\<close>
  unfolding logaddr_to_raw_def valid_logaddr_def
  apply (cases addr1; cases addr2; simp)
  by (smt (verit, ccfv_SIG) Valid_Segment_def add_leD1 index_offset_inj index_offset_upper_bound_0 len_of_addr_cap_def order_le_less_trans segidx.case_eq_if take_bit_nat_eq_self_iff word_of_nat_eq_iff)

definition \<open>rawaddr_to_log T raddr = (@laddr. logaddr_to_raw laddr = raddr \<and> logaddr_type laddr = T \<and> valid_logaddr laddr)\<close>

lemma rawaddr_to_log[simp]:
  \<open>valid_logaddr addr \<Longrightarrow> 0 < MemObj_Size (logaddr_type addr)
    \<Longrightarrow> rawaddr_to_log (logaddr_type addr) (logaddr_to_raw addr) = addr\<close>
  unfolding rawaddr_to_log_def
  by (rule some_equality, simp) (metis logaddr_to_raw_inj) 

end


locale std_sem =
  std_sem_pre where TYPES = TYPES
  for TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N => 'VAL::nonsepable_semigroup) \<times> ('RES_N => 'RES::comm_monoid_mult)) itself\<close>
+ assumes WT_int[simp]: \<open>Well_Type (\<tau>Int b)     = { V_int.mk (b,x)    |x. x < 2^b } \<close>
    and   WT_ptr[simp]: \<open>Well_Type \<tau>Pointer     = { V_pointer.mk addr |addr. valid_rawaddr addr }\<close>
    and   WT_tup[simp]: \<open>Well_Type (\<tau>Tuple ts)  = { V_tup.mk vs       |vs. list_all2 (\<lambda> t v. v \<in> Well_Type t) ts vs }\<close>
    and   WT_arr[simp]: \<open>Well_Type (\<tau>Array n t) = { V_array.mk (t,vs) |vs. length vs = n \<and> list_all (\<lambda>v. v \<in> Well_Type t) vs }\<close>
(*    and Tyof_int[simp]: \<open>Typeof v = \<tau>Int b \<longleftrightarrow> (\<exists>x. v = V_int.mk (b,x))\<close>
    and Tyof_ptr[simp]: \<open>Typeof v = \<tau>Pointer \<longleftrightarrow> (\<exists>rawaddr. v = V_pointer.mk rawaddr)\<close>
    and Tyof_tup[simp]: \<open>Typeof v = \<tau>Tuple (map Typeof vs) \<longleftrightarrow> (\<exists>vs. v = V_tup.mk vs)\<close>
    and Tyof_arr[simp]: \<open>Typeof v = \<tau>Array N t \<longleftrightarrow> (\<exists>vs. v = V_array.mk (t,vs) \<and> length vs = N)\<close> *)

  fixes Resource_Validator :: \<open>'RES_N \<Rightarrow> 'RES set\<close>
  assumes res_valid_mem: \<open>Resource_Validator R_mem.name = R_mem.inject ` Valid_Mem\<close>
    and   res_valid_var: \<open>Resource_Validator R_var.name = {R_var.inject (Fine vars) |vars. finite (dom vars)}\<close>

  fixes In_Mem :: \<open>('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'TY segidx \<Rightarrow> bool\<close>
  defines \<open>In_Mem res seg \<equiv> seg \<in> dom !!(R_mem.get res)\<close>

  fixes Can_EqCompare
  assumes can_eqcmp_ptr[simp]: "Can_EqCompare res (V_pointer.mk rp1) (V_pointer.mk rp2) \<longleftrightarrow>
              (memaddr.segment rp1 = memaddr.segment rp2) \<or> (rp1 = 0) \<or> (rp2 = 0) \<or>
              (In_Mem res (memaddr.segment rp1) \<and> In_Mem res (memaddr.segment rp2))"
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
(*TODO: not all value has zero!!*)
begin

abbreviation \<open>Valid_Type T \<equiv> Inhabited (Well_Type T)\<close>

lemma Valid_Types[simp]:
  \<open>Valid_Type (\<tau>Int n)\<close>
  \<open>Valid_Type \<tau>Pointer\<close>
  \<open>Valid_Type (\<tau>Array n T) \<longleftrightarrow> Valid_Type T\<close>
  \<open>Valid_Type (\<tau>Tuple Ts) \<longleftrightarrow> list_all Valid_Type Ts\<close>
  unfolding Inhabited_def
  apply (simp_all add: Valid_Segment_def  split: memaddr.split segidx.split)
  using less_exp apply blast
  apply (metis Valid_Segment_def segidx.case(2) valid_rawaddr_0)
  apply rule using zero_well_typ apply blast
   apply (elim exE) subgoal for p by (rule exI[where x=\<open>replicate n p\<close>], simp add: list_all_length)
  apply rule apply (metis (mono_tags, lifting) list_all2_conv_all_nth list_all_length)
  by (smt (verit) WT_tup mem_Collect_eq zero_well_typ)



paragraph \<open>Resource Accessor\<close>

definition "Valid_Resource = {R. (\<forall>N. R N \<in> Resource_Validator N)}"

definition sem_read_mem :: \<open>'TY logaddr \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'VAL\<close>
  where \<open>sem_read_mem addr res =
    index_value (memaddr.index addr) (the (the_fine (R_mem.get res) (memaddr.segment addr)))\<close>

definition sem_write_mem :: \<open>'TY logaddr \<Rightarrow> 'VAL \<Rightarrow> ('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('RES_N \<Rightarrow> 'RES)\<close>
  where \<open>sem_write_mem addr val res =
    (let seg = memaddr.segment addr
       ; mem = the_fine (R_mem.get res)
       ; val' = index_mod_value (memaddr.index addr) (\<lambda>_. val) (the (mem seg))
       ; mem' = mem(seg \<mapsto> val')
      in res(R_mem #= Fine mem'))\<close>

end


subsubsection \<open>Pre-built Fiction\<close>

paragraph \<open>Push a map to a location\<close>

definition push_map :: \<open>'a list \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> ('a list \<Rightarrow> 'b::one)\<close>
  where \<open>push_map idx f = (\<lambda>x. if take (length idx) x = idx then f (drop (length idx) x) else 1 )\<close>

lemma push_map_push_map:
  \<open>push_map ia (push_map ib f) = push_map (ia@ib) f\<close>
  unfolding push_map_def fun_eq_iff
  by (smt (verit, ccfv_threshold) add.commute append_eq_append_conv append_eq_conv_conj drop_drop length_append take_add take_drop)

lemma push_map_distrib_mult:
  \<open>push_map idx f * push_map idx g = push_map idx (f * g)\<close>
  for f :: \<open>'a list \<Rightarrow> 'b::monoid_mult\<close>
  unfolding push_map_def fun_eq_iff times_fun_def by simp

lemma push_map_distrib_map_add:
  \<open>push_map idx (f ++ g) = push_map idx f ++ push_map idx g\<close>
  unfolding push_map_def fun_eq_iff map_add_def by simp

lemma push_map_mult_1[simp]:
  \<open>push_map idx f = 1 \<longleftrightarrow> f = 1\<close>
  unfolding push_map_def fun_eq_iff by simp (metis append_eq_conv_conj)

lemma push_map_mult_nil[simp]:
  \<open>push_map [] f = f\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma share_push_map:
  \<open>share n (push_map idx f) = push_map idx (share n f)\<close>
  for f :: \<open>'a list \<Rightarrow> 'b :: share_one\<close>
  unfolding push_map_def fun_eq_iff share_fun_def by simp

lemma (in homo_one) push_map_homo:
  \<open>\<phi> o (push_map idx f) = push_map idx (\<phi> o f)\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma push_map_to_share:
  \<open>push_map idx (to_share o f) = to_share o (push_map idx f)\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma push_map_dom_eq[simp]:
  \<open>dom (push_map idx f) = dom (push_map idx g) \<longleftrightarrow> dom f = dom g\<close>
  unfolding dom_def fun_eq_iff push_map_def set_eq_iff apply simp
  by (metis (full_types) append_eq_conv_conj)


paragraph \<open>Pull a map at a location\<close>

definition pull_map :: \<open>'a list \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> ('a list \<Rightarrow> 'b)\<close>
  where \<open>pull_map idx f = (\<lambda>x. f (idx@x))\<close>

lemma pull_push_map[simp]:
  \<open>pull_map idx (push_map idx f) = f\<close>
  unfolding pull_map_def push_map_def fun_eq_iff by simp

lemma push_pull_map:
  \<open>push_map idx (pull_map idx f) \<subseteq>\<^sub>m f\<close>
  unfolding pull_map_def push_map_def map_le_def dom_def
  by simp (metis append_take_drop_id)

lemma pull_map_1[simp]:
  \<open>pull_map idx 1 = 1\<close> 
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_0[simp]:
  \<open>pull_map idx 0 = 0\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_nil[simp]:
  \<open>pull_map [] f = f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_pull_map[simp]:
  \<open>pull_map a (pull_map b f) = pull_map (b@a) f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_cons:
  \<open>pull_map a (pull_map [b] f) = pull_map (b#a) f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_funcomp:
  \<open>\<phi> 1 = 1 \<Longrightarrow> \<phi> o (pull_map idx f) = pull_map idx (\<phi> o f)\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_homo_mult:
  \<open>pull_map idx (f * g) = pull_map idx f * pull_map idx g\<close>
  unfolding pull_map_def fun_eq_iff
  by (simp add: times_fun)

lemma pull_map_to_share:
  \<open>pull_map idx (to_share o f) = to_share o (pull_map idx f)\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_share:
  \<open>pull_map idx (share n f) = share n (pull_map idx f)\<close>
  unfolding pull_map_def fun_eq_iff share_fun_def by simp

lemma pull_map_sep_disj[simp]:
  \<open>f ## g \<Longrightarrow> pull_map idx f ## pull_map idx g\<close>
  unfolding pull_map_def sep_disj_fun_def by simp


paragraph \<open>Tree Node\<close>

definition node :: \<open>(nat list \<Rightarrow> 'b) list \<Rightarrow> nat list \<Rightarrow> 'b::one\<close>
  where \<open>node L = (\<lambda>idx. case idx of i#idx' \<Rightarrow> (if i < length L then (L!i) idx' else 1) | _ \<Rightarrow> 1)\<close>

lemma share_node:
  \<open>share n (node L) = node (map (share n) L)\<close>
  for L :: \<open>(nat list \<Rightarrow> 'a::share_one) list\<close>
  unfolding node_def fun_eq_iff by (simp add: share_fun_def split: list.split)

lemma pull_map_node:
  \<open>pull_map (i#idx) (node L) = (if i < length L then pull_map idx (L!i) else 1)\<close>
  unfolding node_def pull_map_def fun_eq_iff by simp





locale pre_std_fic =
  std_sem where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N => 'VAL::nonsepable_semigroup) \<times>
               ('RES_N => 'RES::comm_monoid_mult))\<close>
for TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N => 'VAL::nonsepable_semigroup) \<times>
               ('RES_N => 'RES::comm_monoid_mult) \<times> 'SHVAL::sep_algebra) itself\<close>

+ fixes Mapof_Val :: \<open>'VAL \<Rightarrow> nat list \<rightharpoonup> 'VAL\<close>
assumes Mapof_Val_inj: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> Mapof_Val Va = Mapof_Val Vb \<Longrightarrow> Va = Vb\<close>
  and   Mapof_Val_same_dom: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> dom (Mapof_Val Va) = dom (Mapof_Val Vb)\<close>
  and   Mapof_not_1[simp]: \<open>Mapof_Val V \<noteq> 1\<close>
  and   Mapof_Val_pull_step: \<open>valid_idx_step T i \<Longrightarrow> V \<in> Well_Type T
                          \<Longrightarrow> pull_map [i] (Mapof_Val V) = Mapof_Val (idx_step_value i V)\<close>
  and   Mapof_Val_mod_step: \<open>valid_idx_step T i \<Longrightarrow> v \<in> Well_Type T
                         \<Longrightarrow> Mapof_Val (idx_step_mod_value i f v) = Mapof_Val v ++ push_map [i] (Mapof_Val (f (idx_step_value i v)))\<close>
  and   Mapof_Val_tup: \<open>Mapof_Val (V_tup.mk vs) = node (map Mapof_Val vs)\<close>
  and   Mapof_Val_arr: \<open>Mapof_Val (V_array.mk (T,vs)) = node (map Mapof_Val vs)\<close>
begin


lemma Mapof_Val_pull:
  \<open>valid_index T idx \<Longrightarrow> V \<in> Well_Type T \<Longrightarrow> pull_map idx (Mapof_Val V) = Mapof_Val (index_value idx V)\<close>
  apply (induct idx arbitrary: V T; simp)
  using Mapof_Val_pull_step
  by (metis idx_step_value_welltyp pull_map_cons)

lemma total_Mapof_disjoint:
   \<open>g ## (push_map idx (to_share \<circ> h))
\<Longrightarrow> to_share \<circ> f = g * (push_map idx (to_share \<circ> h))
\<Longrightarrow> dom g \<inter> dom (push_map idx (to_share \<circ> h)) = {}\<close>
  using to_share_total_disjoint push_map_to_share by metis

lemma map_add_subsumed_dom:
  \<open>dom f \<subseteq> dom g \<Longrightarrow> f ++ g = g\<close>
  unfolding map_add_def dom_def subset_eq fun_eq_iff apply simp
  by (metis option.case_eq_if option.collapse option.simps(3))

lemma Mapof_Val_mod:
  \<open> valid_index T idx
\<Longrightarrow> v \<in> Well_Type T
\<Longrightarrow> u \<in> Well_Type (index_type idx T)
\<Longrightarrow> Mapof_Val (index_mod_value idx (\<lambda>_. u) v) = Mapof_Val v ++ push_map idx (Mapof_Val u)\<close>
  apply (induct idx arbitrary: u v T; simp)
  using Mapof_Val_same_dom map_add_subsumed_dom apply (metis order_refl)
  by clarify (simp add: idx_step_value_welltyp Mapof_Val_mod_step  push_map_distrib_map_add
                        Mapof_Val_pull_step[symmetric] push_pull_map map_add_subsumed2
                        push_map_push_map)

lemma Mapof_Val_modify_fiction:
   \<open>valid_index T idx
\<Longrightarrow> v \<in> Well_Type T
\<Longrightarrow> u \<in> Well_Type (index_type idx T)
\<Longrightarrow> u'\<in> Well_Type (index_type idx T)
\<Longrightarrow> g ## (push_map idx (to_share \<circ> Mapof_Val u))
\<Longrightarrow> to_share \<circ> (Mapof_Val v) = g * (push_map idx (to_share \<circ> Mapof_Val u))
\<Longrightarrow> to_share \<circ> (Mapof_Val (index_mod_value idx (\<lambda>_. u') v)) = g * (push_map idx (to_share \<circ> Mapof_Val u'))\<close>
  apply (simp add: Mapof_Val_mod to_share_funcomp_map_add push_map_to_share
      times_fun_map_add_right total_Mapof_disjoint[simplified push_map_to_share]
      Mapof_Val_same_dom push_map_dom_eq)
  subgoal premises prems proof -
    have \<open>dom g \<inter> dom (to_share \<circ> push_map idx (Mapof_Val u)) = {}\<close>
      using prems to_share_total_disjoint by blast
    moreover have t1:
      \<open>dom (to_share \<circ> push_map idx (Mapof_Val u)) = dom (to_share \<circ> push_map idx (Mapof_Val u'))\<close>
      using prems by (metis Mapof_Val_same_dom dom_map_option_comp push_map_dom_eq)
    ultimately have \<open>dom g \<inter> dom (to_share \<circ> push_map idx (Mapof_Val u')) = {}\<close> by metis
    note [simp] = times_fun_map_add_right[OF this]
    show ?thesis by simp (metis t1 map_add_subsumed_dom order_eq_refl)
  qed
  done
(* lemma pull_map_share_Mapof_not_eq_1[simp]:
  \<open>valid_index (Typeof v) idx \<Longrightarrow> pull_map idx (share n (to_share \<circ> Mapof_Val v)) = 1 \<longleftrightarrow> n = 0\<close>
  by (cases \<open>n = 0\<close>; simp add: pull_map_share pull_map_to_share Mapof_Val_pull)
*)


lemma map_add_restrict_itself [simp]: \<open>(f ++ g) |` dom g = g\<close>
  unfolding fun_eq_iff restrict_map_def map_add_def
  by (simp add: domIff option.case_eq_if)

lemma Mapof_Val_inj_plus:
  \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> f ++ Mapof_Val Va = f ++ Mapof_Val Vb \<Longrightarrow> Va = Vb\<close>
proof (rule Mapof_Val_inj, assumption)
  assume tyA: \<open>Va \<in> Well_Type T\<close>
     and tyB: \<open>Vb \<in> Well_Type T\<close>
     and feq: \<open>f ++ Mapof_Val Va = f ++ Mapof_Val Vb\<close>
  then have \<open>(f ++ Mapof_Val Va) |` dom (Mapof_Val Va) = (f ++ Mapof_Val Vb) |` dom (Mapof_Val Vb)\<close>
    using Mapof_Val_same_dom by metis 
  note this [simplified]
  then show \<open>Mapof_Val Va = Mapof_Val Vb\<close> .
qed

definition \<open>Valof_Map TY M = (@V. (\<exists>f. f ++ Mapof_Val V = M) \<and> V \<in> Well_Type TY)\<close>

lemma Valof_Map_append[simp]:
  \<open>v \<in> Well_Type T \<Longrightarrow> Valof_Map T (f ++ Mapof_Val v) = v\<close>
  unfolding Valof_Map_def
  using someI[where P=\<open>\<lambda>V. (\<exists>fa. fa ++ Mapof_Val V = f ++ Mapof_Val v) \<and> V \<in> Well_Type T\<close> and x=v, simplified]
        Mapof_Val_inj_plus
  by (metis (no_types, lifting) Mapof_Val_same_dom map_add_restrict_itself) 

lemmas Valof_Map[simp] = Valof_Map_append[where f = \<open>Map.empty\<close>, simplified]




definition \<open>share_val_fiction TY =
      Fiction (\<lambda>m. if m = 1 then {None} else {Some v |v. v \<in> Well_Type TY \<and> to_share o Mapof_Val v = m})\<close>

lemma share_val_fiction[simp]:
  \<open>\<I> (share_val_fiction TY) = (\<lambda>m. if m = 1 then {None} else {Some v |v. v \<in> Well_Type TY \<and> to_share o Mapof_Val v = m})\<close>
  unfolding share_val_fiction_def by (rule Fiction_inverse) (simp add: Fictional_def one_set_def)


paragraph \<open>Basic fictions for resource elements\<close>

definition "fiction_mem I = Fiction (\<lambda>x. { 1(R_mem #= y) |y. y \<in> \<I> I x})"
lemma fiction_mem_\<I>:
  "\<I> (fiction_mem I) = (\<lambda>x. { 1(R_mem #= y) |y. y \<in> \<I> I x})"
  unfolding fiction_mem_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def)

definition "fiction_var I = Fiction (\<lambda>x. { 1(R_var #= y) |y. y \<in> \<I> I x})"
lemma fiction_var_\<I>[simp]:
  "\<I> (fiction_var I) = (\<lambda>x. { 1(R_var #= y) |y. y \<in> \<I> I x})"
  unfolding fiction_var_def
  by (rule Fiction_inverse) (auto simp add: Fictional_def one_set_def)


definition "share_mem' = 
              fiction.pointwise' (\<lambda>seg. fiction.fine (share_val_fiction (segidx.layout seg)))"

definition "share_mem = fiction_mem (fiction.defined (
              fiction.pointwise' (\<lambda>seg. fiction.fine (share_val_fiction (segidx.layout seg)))))"

lemma share_mem_def':
  \<open>share_mem = fiction_mem (fiction.defined share_mem')\<close>
  unfolding share_mem_def share_mem'_def ..

definition "exclusive_var = fiction_var fiction.it"



end


fiction_space (in pre_std_fic) std_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> =
  FIC_mem :: share_mem
  FIC_var :: exclusive_var


subsubsection \<open>Standard Settings\<close>

locale std = std_fic
  where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup) \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult) \<times> 'SHVAL::sep_algebra)\<close>
    and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
    and TYPE'REP = \<open>TYPE('FIC::{no_inverse,comm_monoid_mult})\<close> 
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC) \<times> 'SHVAL::sep_algebra) itself\<close>
begin

abbreviation "INTERP_RES fic \<equiv> Valid_Resource \<inter> S_Assert (Fic_Space fic) \<inter> \<I> INTERP fic"

definition INTERP_COMP :: \<open>('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('RES_N \<Rightarrow> 'RES) set\<close>
  where "INTERP_COMP T = { res. \<exists>fic. fic \<in> T \<and> res \<in> INTERP_RES fic }"

lemma INTERP_COMP[\<phi>expns]:
  \<open>res \<in> INTERP_COMP T \<longleftrightarrow> (\<exists>fic. fic \<in> T \<and> res \<in> INTERP_RES fic)\<close>
  unfolding INTERP_COMP_def by simp

lemma INTERP_COMP_subset[intro, simp]: \<open>A \<subseteq> B \<Longrightarrow> INTERP_COMP A \<subseteq> INTERP_COMP B\<close>
  unfolding INTERP_COMP_def subset_iff by simp blast

lemma INTERP_COMP_plus[iff]:
  \<open>INTERP_COMP (A + B) = INTERP_COMP A + INTERP_COMP B\<close>
  unfolding INTERP_COMP_def plus_set_def by simp blast

lemma INTERP_COMP_empty[intro, simp]:
  \<open>S = {} \<Longrightarrow> INTERP_COMP S = {}\<close>
  unfolding INTERP_COMP_def set_eq_iff by simp

lemma INTERP_mono:
  \<open> Fic_Space fic
\<Longrightarrow> Fic_Space x
\<Longrightarrow> dom1 res \<inter> dom1 p = {}
\<Longrightarrow> dom1 fic \<inter> dom1 x = {}
\<Longrightarrow> res \<in> \<I> INTERP fic
\<Longrightarrow> p \<in> \<I> INTERP x
\<Longrightarrow> res * p \<in> \<I> INTERP (fic * x)\<close>
  unfolding INTERP_def Fic_Space_def
  apply (simp add: dom1_mult_disjoint times_fun prod.union_disjoint
                   disjoint_dom1_eq_1[of fic x])
  using times_set_I by blast



lemma FIC_var_split: \<open>Fic_Space fic \<Longrightarrow>
    \<I> INTERP (fic * FIC_var.mk vars) = \<I> INTERP fic * {R_var.mk vars}\<close>
  apply (subst FIC_var.interp_split; simp add: exclusive_var_def R_var.mk_homo_mult)
  by (subst FIC_var.interp_split[where f = fic]; simp add: exclusive_var_def
      set_mult_single[symmetric] mult.assoc)

lemma R_var_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    R_var.clean res \<in> Valid_Resource \<and> (\<exists>vars. res R_var.name = R_var.inject (Fine vars) \<and> finite (dom vars))\<close>
  by (subst R_var.split, simp add: Valid_Resource_def times_fun_def res_valid_var one_fine_def) blast

lemma R_var_valid_split':
   \<open>NO_MATCH (R_var.clean res') res \<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow>
    R_var.clean res \<in> Valid_Resource \<and> (\<exists>vars. res R_var.name = R_var.inject (Fine vars) \<and> finite (dom vars))\<close>
  using R_var_valid_split .

lemma R_mem_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    R_mem.clean res \<in> Valid_Resource \<and> (\<exists>m. res R_mem.name = R_mem.inject m \<and> m \<in> Valid_Mem)\<close>
  by (subst R_mem.split, simp add: Valid_Resource_def times_fun_def res_valid_mem image_iff) blast

lemma R_mem_valid_split': \<open>NO_MATCH (R_mem.clean res') res \<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow>
    R_mem.clean res \<in> Valid_Resource \<and> (\<exists>m. res R_mem.name = R_mem.inject m \<and> m \<in> Valid_Mem)\<close>
  using R_mem_valid_split .


(*
lemma \<open>Fic_Space fic \<Longrightarrow>
      res \<in> INTERP_RES (fic * FIC_mem.mk (1(seg := Fine (push_map idx (to_share o Mapof_Val val)))))
  \<longrightarrow> (\<exists>m v. R_mem.get res = Fine m \<and> m seg = Some v \<and> v \<in> Well_Type (segidx.layout seg) \<and> index_value idx v = val)\<close>

 
lemma \<open>Fic_Space fic \<Longrightarrow> n \<noteq> 0 \<Longrightarrow>
      res \<in> INTERP_RES (fic * FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Mapof_Val val))))))
  \<longrightarrow> (\<exists>m v. R_mem.get res = Fine m \<and> m seg = Some v \<and> v \<in> Well_Type (segidx.layout seg) \<and> index_value idx v = val)\<close>
  apply (subst FIC_mem.interp_split; simp add: share_mem_def times_set_def)
  apply (subst R_mem_valid_split)
  apply (auto simp add: R_mem.proj_homo_mult Valid_Mem_def R_mem.mult_strip_inject_011
                        mult_strip_fine_011 times_fun[where x = seg] )
  subgoal premises prems for remain_res mem remain proof -
    note [simp] = mult_strip_fine_011 times_fun[where x = seg]
    have \<open>remain seg ## mem seg\<close> using \<open>remain ## mem\<close> by (simp add: sep_disj_fun_def) 
    show ?thesis
      apply (insert \<open>\<forall>x. \<exists>y. _\<close>[THEN spec[where x = seg], simplified]
                    \<open>remain seg ## mem seg\<close>
                    \<open>\<forall>seg \<in> dom _. _\<close>[unfolded Ball_def, THEN spec[where x= seg], simplified])
      apply (auto simp add: share_val_fiction \<open>n \<noteq> 0\<close>)
      subgoal premises prems2 for other_part Val proof -
        let \<open>?lhs = ?rhs\<close> = \<open>to_share \<circ> Mapof_Val Val = other_part * push_map idx (share n (to_share \<circ> Mapof_Val val))\<close>
        from \<open>?lhs = ?rhs\<close> have \<open>strip_share o pull_map idx ?lhs = strip_share o pull_map idx ?rhs\<close> by fastforce
        note this[simplified pull_map_to_share Mapof_Val_pull strip_share_share_funcomp
                             pull_map_homo_mult pull_push_map]
        thm prems2
        term Valof_Map

  thm times_fun[where x = seg]
  thm R_mem.split

*)


definition "View_Shift u v \<longleftrightarrow> INTERP_RES u \<subseteq> INTERP_RES v "

end


(* type_synonym logaddr = "nat memaddr" *)


subsection \<open>Monadic Formalization\<close>

datatype 'a sem_value = sem_value (dest_sem_value: 'a)
typedecl unreachable

datatype ('ret,'RES_N,'RES) state =
      Success \<open>'ret sem_value\<close> (resource: "('RES_N \<Rightarrow> 'RES)")
    | Exception (resource: "('RES_N \<Rightarrow> 'RES)")
    | Fail | PartialCorrect

hide_const(open) resource

text\<open> The basic state of the \<phi>-system virtual machine is represented by type "('a::lrep) state"}.
  The valid state `Success` essentially has two major form, one without registers and another one with them,
      \<^item> "StatOn (x1, x2, \<cdots>, xn, void)",
  where "(x1, x2, \<cdots>, xn, void)" represents the stack in the state, with @{term x\<^sub>i} as the i-th element on the stack.
  The @{term STrap} is trapped state due to invalid operations like zero division.
  The negative state @{term PartialCorrect} represents the admissible error situation that is not considered in partial correctness.
  For example, @{term PartialCorrect} may represents an admissible crash, and in that case the partial correctness certifies that
    ``if the program exits normally, the output would be correct''.\<close>

declare state.split[split]

type_synonym ('ret,'RES_N,'RES) proc = "('RES_N \<Rightarrow> 'RES) \<Rightarrow> ('ret,'RES_N,'RES) state"
type_synonym ('arg, 'ret,'RES_N,'RES) M = "'arg sem_value \<Rightarrow> ('ret,'RES_N,'RES) proc"

definition bind :: "('a,'RES_N,'RES) proc \<Rightarrow> ('a,'b,'RES_N,'RES) M \<Rightarrow> ('b,'RES_N,'RES) proc"  ("_ \<bind>/ _" [76,75] 75)
  where "bind f g = (\<lambda>res. case f res of Success v x \<Rightarrow> g v x | Exception x \<Rightarrow> Exception x
                                       | Fail \<Rightarrow> Fail | PartialCorrect \<Rightarrow> PartialCorrect)"

abbreviation bind' ("_ \<ggreater>/ _" [76,75] 75)
  where \<open>bind' f g \<equiv> (f \<bind> (\<lambda>_. g))\<close>

lemma proc_bind_SKIP[simp]:
  "f \<bind> Success \<equiv> f"
  "Success any \<ggreater> f \<equiv> f"
  "(g \<ggreater> Success any) \<ggreater> f \<equiv> g \<ggreater> f"
  "(\<lambda>v. Success v \<bind> h) \<equiv> h"
  unfolding bind_def atomize_eq fun_eq_iff by simp+

lemma proc_bind_assoc:
  "((A \<bind> B) \<bind> C) = (A \<bind> (\<lambda>x. B x \<bind> C))"
  unfolding bind_def fun_eq_iff by simp


abbreviation \<open>\<phi>V_nil \<equiv> sem_value ()\<close>
definition \<open>\<phi>V_pair x y = sem_value (dest_sem_value x, dest_sem_value y)\<close>
definition \<open>\<phi>V_fst x = map_sem_value fst x\<close>
definition \<open>\<phi>V_snd x = map_sem_value snd x\<close>

lemma \<phi>V_simps[simp]:
  \<open>\<phi>V_pair (\<phi>V_fst v) (\<phi>V_snd v) = v\<close>
  \<open>\<phi>V_fst (\<phi>V_pair u y) = u\<close>
  \<open>\<phi>V_snd (\<phi>V_pair x u) = u\<close>
  unfolding \<phi>V_pair_def \<phi>V_fst_def \<phi>V_snd_def by (cases v, simp)+

section \<open>Specification Framework\<close>

type_synonym ('RES_N,'RES) assn = "('RES_N \<Rightarrow> 'RES) set" \<comment> \<open>assertion\<close>

subsection \<open>Preliminary\<close>

subsubsection \<open>Predicates for Total Correctness & Partial Correctness\<close>

context std_sem begin

definition StrictStateTy :: "('ret sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('RES_N,'RES) assn
                          \<Rightarrow> ('ret,'RES_N,'RES) state set" ("!\<S>")
  where "!\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val | Exception x \<Rightarrow> x \<in> E
                              | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> False}"
definition LooseStateTy  :: "('ret sem_value \<Rightarrow> ('RES_N,'RES) assn)
                          \<Rightarrow> ('RES_N,'RES) assn
                          \<Rightarrow> ('ret,'RES_N,'RES) state set" ("\<S>")
  where  "\<S> T E = {s. case s of Success val x \<Rightarrow> x \<in> T val | Exception x \<Rightarrow> x \<in> E
                              | Fail \<Rightarrow> False | PartialCorrect \<Rightarrow> True}"

lemma StrictStateTy_expn[iff,\<phi>def]:
        "Success vs x \<in> !\<S> T E \<equiv> x \<in> T vs" "Exception x \<in> !\<S> T E \<equiv> x \<in> E"
        "\<not> (Fail \<in> !\<S> T E)"  "\<not> (PartialCorrect \<in> !\<S> T E)"
  and LooseStateTy_expn[iff,\<phi>def]:
        "Success vs x \<in> \<S> T E \<equiv> x \<in> T vs" "Exception x \<in> \<S> T E \<equiv> x \<in> E"
        "\<not> (Fail \<in> \<S> T E)"  "(PartialCorrect \<in> \<S> T E)"
  by (simp_all add: StrictStateTy_def LooseStateTy_def)
lemma LooseStateTy_expn' :
    "x \<in> \<S> T E \<longleftrightarrow> x = PartialCorrect \<or> (\<exists>x' vs. x = Success vs x' \<and> x' \<in> T vs) \<or> (\<exists>x'. x = Exception x' \<and> x' \<in> E)"
  by (cases x) simp_all

lemma StrictStateTy_elim[elim]:
    "s \<in> !\<S> T E
\<Longrightarrow> (\<And>x vs. s = Success vs x \<Longrightarrow> x \<in> T vs \<Longrightarrow> C)
\<Longrightarrow> (\<And>x. s = Exception x \<Longrightarrow> x \<in> E \<Longrightarrow> C)
\<Longrightarrow> C" by (cases s) auto
lemma StrictStateTy_intro[intro]:
    " x \<in> T vs \<Longrightarrow> Success vs x \<in> !\<S> T E"
    " x \<in> E \<Longrightarrow> Exception x \<in> !\<S> T E"
  by simp_all
lemma LooseStateTy_E[elim]:
    "s \<in> \<S> T E
\<Longrightarrow> (\<And>x vs. s = Success vs x \<Longrightarrow> x \<in> T vs \<Longrightarrow> C)
\<Longrightarrow> (\<And>x. s = Exception x \<Longrightarrow> x \<in> E \<Longrightarrow> C)
\<Longrightarrow> (s = PartialCorrect \<Longrightarrow> C)
\<Longrightarrow> C"
  by (cases s) auto
lemma LooseStateTy_I[intro]:
  "x \<in> T vs \<Longrightarrow> Success vs x \<in> \<S> T E"
  "x \<in> E \<Longrightarrow> Exception x \<in> \<S> T E"
  "PartialCorrect \<in> \<S> T E"
  by simp_all

lemma LooseStateTy_upgrade:
  "s \<in> \<S> T E \<Longrightarrow> s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T E"
  by (cases s) auto
lemma StrictStateTy_degrade: "s \<in> !\<S> T E \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto
lemma LooseStateTy_introByStrict: "(s \<noteq> PartialCorrect \<Longrightarrow> s \<in> !\<S> T E) \<Longrightarrow> s \<in> \<S> T E" by (cases s) auto

lemma StrictStateTy_subset[intro]:
  \<open>(\<And>vs. A vs \<subseteq> A' vs) \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> !\<S> A E \<subseteq> !\<S> A' E'\<close>
  unfolding subset_iff StrictStateTy_def by simp
lemma LooseStateTy_subset[intro]:
  \<open>(\<And>vs. A vs \<subseteq> A' vs) \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> \<S> A E \<subseteq> \<S> A' E'\<close>
  unfolding subset_iff LooseStateTy_def by simp

lemma LooseStateTy_plus[iff]:
(*  \<open>\<S> (A + B) E   = \<S> A E + \<S> B E\<close> *)
  \<open>\<S> X (EA + EB) = \<S> X EA + \<S> X EB\<close>
  unfolding set_eq_iff LooseStateTy_def by simp_all
lemma StrictStateTy_plus[iff]:
(*  \<open>!\<S> (A + B) E   = !\<S> A E  + !\<S> B E\<close> *)
  \<open>!\<S> X (EA + EB) = !\<S> X EA + !\<S> X EB\<close>
  unfolding set_eq_iff StrictStateTy_def by simp_all

end

abbreviation (in std) \<open>Void \<equiv> (1::('FIC_N,'FIC) assn)\<close>


(* subsubsection \<open>Stack Element and Communicative Monoid Resource\<close>

consts Ele :: " 'a set \<Rightarrow> ('VAL,'FIC_N,'FIC) assn " ("ELE _" [17] 16)

context std begin

definition Val_Ele :: " 'VAL set \<Rightarrow> ('VAL,'FIC_N,'FIC) assn " ("VAL _" [17] 16)
  where "(VAL S) = { ([v], 1) | v. v \<in> S } "

adhoc_overloading Ele Val_Ele

lemma [\<phi>expns]:
  "(s,h) \<in> (VAL V) \<longleftrightarrow> h = 1 \<and> (\<exists>v. s = [v] \<and> v \<in> V)"
  unfolding Val_Ele_def by simp blast

lemma Val_Ele_inhabited[elim!]:
  "Inhabited (VAL T) \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: pair_exists \<phi>expns)

definition Obj_Ele :: "('FIC_N \<Rightarrow> 'FIC) set \<Rightarrow> ('VAL,'FIC_N,'FIC) assn " ("OBJ _" [17] 16)
  where "(OBJ T) = { ([],h) | h. h \<in> T } "

adhoc_overloading Ele Obj_Ele

lemma [\<phi>expns]: "(s,h) \<in> (OBJ T) \<longleftrightarrow> s = [] \<and> h \<in> T"
  unfolding Obj_Ele_def by simp

lemma Obj_Ele_inhabited[elim!]:
  "Inhabited (OBJ T) \<Longrightarrow> (Inhabited T \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: pair_exists \<phi>expns)

lemma OBJ_comm: \<open>S * (OBJ T) = (OBJ T) * S\<close>
  unfolding Obj_Ele_def times_set_def set_eq_iff apply (simp add: times_list_def)
  using mult.commute by blast

end
*)
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

subsection \<open>Assertion\<close>

context std begin

definition \<phi>Procedure :: "('ret,'RES_N,'RES) proc \<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> ('ret sem_value \<Rightarrow> ('FIC_N,'FIC) assn) \<Rightarrow> ('FIC_N,'FIC) assn \<Rightarrow> bool"
    ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s _ \<rbrace>))" [101,2,2,2] 100)
  where [\<phi>def]:"\<phi>Procedure f T U E \<longleftrightarrow>
    (\<forall>comp R. comp \<in> INTERP_COMP (R * T) \<longrightarrow> f comp \<in> \<S> (\<lambda>vs. INTERP_COMP (R * U vs)) (INTERP_COMP (R * E)))"

abbreviation \<phi>Procedure_no_exception ("(2\<^bold>p\<^bold>r\<^bold>o\<^bold>c _/ (2\<lbrace> _/ \<longmapsto> _ \<rbrace>))" [101,2,2] 100)
  where \<open>\<phi>Procedure_no_exception f T U \<equiv> \<phi>Procedure f T U 0\<close>

subsubsection \<open>Essential Hoare Rules\<close>

lemma \<phi>SKIP[simp,intro!]: "\<^bold>p\<^bold>r\<^bold>o\<^bold>c Success v \<lbrace> T v \<longmapsto> T \<rbrace>" unfolding \<phi>Procedure_def by simp

lemma \<phi>SEQ:
   "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>
\<Longrightarrow> (\<And>vs. \<^bold>p\<^bold>r\<^bold>o\<^bold>c g vs \<lbrace> B vs \<longmapsto> C \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>)
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c (f \<bind> g) \<lbrace> A \<longmapsto> C \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace>"
  unfolding \<phi>Procedure_def bind_def by (auto 0 4)

lemma \<phi>frame:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s R * E \<rbrace>"
  unfolding \<phi>Procedure_def
  apply clarify subgoal premises prems for comp R'
    using prems(1)[THEN spec[where x=comp], THEN spec[where x=\<open>R' * R\<close>],
          simplified mult.assoc, THEN mp, OF prems(2)] . .

lemma \<phi>frame0:
  "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A \<longmapsto> B \<rbrace> \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> R * A \<longmapsto> \<lambda>ret. R * B ret \<rbrace>"
  using \<phi>frame[where E=0, simplified] .

lemma \<phi>CONSEQ:
   "\<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A  \<longmapsto> B  \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E  \<rbrace>
\<Longrightarrow> A' \<subseteq> A
\<Longrightarrow> (\<And>ret. B ret \<subseteq> B' ret)
\<Longrightarrow> E \<subseteq> E'
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c f \<lbrace> A' \<longmapsto> B' \<^bold>t\<^bold>h\<^bold>r\<^bold>o\<^bold>w\<^bold>s E' \<rbrace>"
  unfolding \<phi>Procedure_def
  apply clarify
  subgoal premises prems for comp R proof -
    have \<open>INTERP_COMP (R * A') \<subseteq> INTERP_COMP (R * A)\<close>
      apply (rule INTERP_COMP_subset; rule times_set_subset)
      using prems by blast
    moreover have \<open>\<S> (\<lambda>vs. INTERP_COMP (R * B vs)) (INTERP_COMP (R * E))
       \<subseteq> \<S> (\<lambda>vs. INTERP_COMP (R * B' vs)) (INTERP_COMP (R * E'))\<close>
      apply (rule LooseStateTy_subset; rule INTERP_COMP_subset; rule times_set_subset)
      using prems by blast+
    ultimately show ?thesis using prems by blast
  qed .
end


(* definition Map :: " 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set " where "Map A B = {f. \<forall>a. a \<in> A \<longrightarrow> f a \<in> B }"
definition Map' :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" ("(2\<^bold>m\<^bold>a\<^bold>p _/ \<lbrace>(2 _/ \<longmapsto> _ )\<rbrace>)" [101,2,2] 100)
  where [\<phi>def]: "\<^bold>m\<^bold>a\<^bold>p f \<lbrace> T \<longmapsto> U \<rbrace> \<equiv> \<forall>a. a \<in> T \<longrightarrow> f a \<in> U" *)


end
