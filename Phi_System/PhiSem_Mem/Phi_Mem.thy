theory Phi_Mem
  imports Phi_System.PhiSem_Formalization_Tools
begin

section \<open>Semantic\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype mem_ty = std_ty +
  T_pointer :: unit

context mem_ty begin
abbreviation \<open>\<tau>Pointer \<equiv> T_pointer.mk ()\<close>
end

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

virtual_datatype 'TY mem_val :: "nonsepable_semigroup" = 'TY std_val +
  V_pointer :: \<open>'TY rawaddr\<close>


subsubsection \<open>Resource\<close>

type_synonym ('TY,'VAL) R_mem' = \<open>('TY segidx \<rightharpoonup> 'VAL)\<close>
type_synonym ('TY,'VAL) R_mem = \<open>('TY,'VAL) R_mem' ?\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) mem_res = ('VAL,'TY) std_res
  R_mem :: \<open>('TY,'VAL) R_mem\<close>


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