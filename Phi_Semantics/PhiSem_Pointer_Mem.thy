theory PhiSem_Pointer_Mem
  imports Phi_System.PhiSem_Formalization_Tools "HOL-Library.Word"
begin

section \<open>Semantic\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype \<phi>mem_ty = \<phi>empty_ty +
  T_pointer :: unit

context \<phi>mem_ty begin
abbreviation \<open>pointer \<equiv> T_pointer.mk ()\<close>
end

debt_axiomatization T_pointer :: \<open>unit type_entry\<close>
  where \<phi>mem_ty_ax: \<open>\<phi>mem_ty TY_CONS_OF T_pointer\<close>

interpretation \<phi>mem_ty TY_CONS_OF _ _ T_pointer using \<phi>mem_ty_ax .


subsubsection \<open>Value\<close>

paragraph \<open>Memory Address\<close>

consts addrspace_bits :: "nat" \<comment> \<open>The bit length of the memory address space, in unit of bits\<close>
specification (addrspace_bits) addrspace_bits_L0: "0 < addrspace_bits" by auto

typedecl addr_cap


instantiation addr_cap :: len begin
definition [simp]: "len_of_addr_cap (_::addr_cap itself) = addrspace_bits"
instance apply standard using addrspace_bits_L0 by simp
end

type_synonym size_t = \<open>addr_cap word\<close>
abbreviation to_size_t :: \<open>nat \<Rightarrow> size_t\<close> where \<open>to_size_t \<equiv> of_nat\<close>


declare [ [typedef_overloaded] ]

datatype segidx = Null | Segment nat \<comment> \<open>nonce\<close> (layout: TY)
  \<comment> \<open>The nonce itself is not an identifier, but (nonce \<times> layout) is.\<close>

hide_const (open) layout

datatype 'index memaddr = memaddr (segment: segidx) (index: 'index ) (infixl "|:" 60)

declare [ [typedef_overloaded = false] ]

declare memaddr.sel[iff]
hide_const (open) segment index

type_synonym logaddr = \<open>nat list memaddr\<close> (* the index of logaddr is non empty *)
type_synonym rawaddr = \<open>size_t memaddr\<close>

instantiation segidx :: zero begin
definition [simp]: "zero_segidx = Null"
instance ..
end

instantiation memaddr :: (zero) zero begin
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
  \<open>infinite (UNIV :: segidx set)\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>(UNIV :: segidx set)\<close>
        and f = \<open>\<lambda>n. Segment n undefined\<close>]
  by (meson infinite_UNIV_char_0 injI segidx.inject top_greatest)

lemma segidx_infinite_TY:
  \<open>infinite {a. segidx.layout a = TY}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{a. segidx.layout a = TY}\<close>
        and f = \<open>\<lambda>n. Segment n TY\<close>]
  using inj_def by fastforce


abbreviation shift_addr :: "'idx memaddr \<Rightarrow> ('idx::monoid_add) \<Rightarrow> 'idx memaddr" (infixl "||+" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. x + delta) addr"

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

virtual_datatype \<phi>mem_val :: "sep_magma" = \<phi>empty_val +
  V_pointer :: rawaddr

debt_axiomatization V_pointer :: \<open>rawaddr value_entry\<close>
  where \<phi>mem_val_ax: \<open>\<phi>mem_val VAL_CONS_OF V_pointer\<close>

interpretation \<phi>mem_val VAL_CONS_OF _ _ V_pointer using \<phi>mem_val_ax .



subsubsection \<open>Resource\<close>

type_synonym R_mem = \<open>(segidx \<rightharpoonup> VAL nonsepable)\<close>

resource_space \<phi>mem_res = \<phi>empty_res +
  R_mem :: R_mem

debt_axiomatization R_mem :: \<open>R_mem resource_entry\<close>
  where R_mem_ax: \<open>\<phi>mem_res R_mem\<close>

interpretation \<phi>mem_res R_mem using R_mem_ax .



subsection \<open>Semantics\<close>

datatype ('TY,'VAL) \<M> = \<M>
  (size_of:        \<open>'TY \<Rightarrow> nat\<close>)
  (valid_idx_step: \<open>'TY \<Rightarrow> nat \<Rightarrow> bool\<close>)
  (idx_step_type:  \<open>nat \<Rightarrow> 'TY \<Rightarrow> 'TY\<close>)
  (idx_step_value: \<open>nat \<Rightarrow> 'VAL \<Rightarrow> 'VAL\<close>)
  (idx_step_mod_value: \<open>nat \<Rightarrow> ('VAL \<Rightarrow> 'VAL) \<Rightarrow> 'VAL \<Rightarrow> 'VAL\<close>)
  (idx_step_offset: \<open>'TY \<Rightarrow> nat \<Rightarrow> nat\<close>)

hide_const (open) size_of valid_idx_step idx_step_type idx_step_value
  idx_step_mod_value idx_step_offset

locale mem_setting =
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

fixes \<M> :: \<open>('TY,'VAL) \<M>\<close>
  assumes memobj_size_arr    : \<open>\<M>.size_of \<M> (\<tau>Array N T) = N * \<M>.size_of \<M> T\<close>
    and   memobj_size_step   : \<open>\<M>.valid_idx_step \<M> T i \<Longrightarrow> \<M>.size_of \<M> (idx_step_type i T) \<le> \<M>.size_of \<M> T\<close>
    and   idx_step_type_measure: \<open>\<M>.valid_idx_step \<M> T i \<Longrightarrow> type_measure (\<M>.idx_step_type \<M> i T) < type_measure T\<close>
    and   idx_step_type_tup  : \<open>i < length tys \<Longrightarrow> \<M>.idx_step_type \<M> i (\<tau>Tuple tys) = tys!i \<close>
    and   idx_step_type_arr  : \<open>i \<le> N \<Longrightarrow> \<M>.idx_step_type \<M> i (\<tau>Array N T) = T\<close>
    and   valid_idx_step_tup : \<open>\<M>.valid_idx_step \<M> (\<tau>Tuple tys) i \<longleftrightarrow> i < length tys\<close>
    and   valid_idx_step_arr : \<open>\<M>.valid_idx_step \<M> (\<tau>Array N T) i \<longleftrightarrow> i < N\<close>
    and   idx_step_value_welltyp: \<open>\<M>.valid_idx_step \<M> T i \<Longrightarrow> v \<in> Well_Type T \<Longrightarrow> \<M>.idx_step_value \<M> i v \<in> Well_Type (\<M>.idx_step_type \<M> i T)\<close>
    and   idx_step_value_tup : \<open>\<M>.idx_step_value \<M> i (V_tup.mk vs)   = vs!i\<close>
    and   idx_step_value_arr : \<open>\<M>.idx_step_value \<M> i (V_array.mk (T,vs)) = vs!i\<close>
    and   idx_step_mod_value : \<open>\<M>.valid_idx_step \<M> T i
                            \<Longrightarrow> \<M>.valid_idx_step \<M> T j
                            \<Longrightarrow> v \<in> Well_Type T
                            \<Longrightarrow> \<M>.idx_step_value \<M> i (\<M>.idx_step_mod_value \<M> j f v) =
                                  (if i = j then f (\<M>.idx_step_value \<M> j v) else \<M>.idx_step_value \<M> i v) \<close>
    and   idx_step_mod_value_welltyp: \<open>\<M>.valid_idx_step \<M> T i
                                   \<Longrightarrow> v \<in> Well_Type T
                                   \<Longrightarrow> f (\<M>.idx_step_value \<M> i v) \<in> Well_Type (\<M>.idx_step_type \<M> i T)
                                   \<Longrightarrow> \<M>.idx_step_mod_value \<M> i f v \<in> Well_Type T\<close>
    and   idx_step_mod_value_tup : \<open>\<M>.idx_step_mod_value \<M> i f (V_tup.mk vs) = V_tup.mk (vs[i := f (vs!i)])\<close>
    and   idx_step_mod_value_arr : \<open>\<M>.idx_step_mod_value \<M> i f (V_array.mk (T,vs)) = V_array.mk (T,vs[i := f (vs!i)])\<close>
    and   idx_step_offset_arr: \<open>\<M>.idx_step_offset \<M> (\<tau>Array N T) i = i * \<M>.size_of \<M> T\<close>
    and   idx_step_offset_size:\<open>\<M>.valid_idx_step \<M> T i \<Longrightarrow> \<M>.idx_step_offset \<M> T i + \<M>.size_of \<M> (\<M>.idx_step_type \<M> i T) \<le> \<M>.size_of \<M> T\<close>
    and   idx_step_offset_disj:\<open>\<M>.valid_idx_step \<M> T i \<Longrightarrow> \<M>.valid_idx_step \<M> T j \<Longrightarrow>
                                \<M>.idx_step_offset \<M> T i \<le> \<M>.idx_step_offset \<M> T j \<Longrightarrow>
                                \<M>.idx_step_offset \<M> T j < \<M>.idx_step_offset \<M> T i + \<M>.size_of \<M> (\<M>.idx_step_type \<M> i T) \<Longrightarrow>
                                i = j\<close>




end