theory Phi_AgMem
  imports Phi_Aggregate NuSys NuInstructions
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype agmem_ty = aggregate_ty +
  T_pointer :: unit

context agmem_ty begin
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
  then show False by presburger
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

virtual_datatype 'TY agmem_val :: "nonsepable_semigroup" = 'TY aggregate_val +
  V_pointer :: \<open>'TY rawaddr\<close>


subsubsection \<open>Resource\<close>

type_synonym ('TY,'VAL) R_mem' = \<open>('TY segidx \<rightharpoonup> 'VAL)\<close>
type_synonym ('TY,'VAL) R_mem = \<open>('TY,'VAL) R_mem' ?\<close>

resource_space ('VAL::"nonsepable_semigroup",'TY) agmem_res = ('VAL,'TY) std_res +
  R_mem :: \<open>('TY,'VAL) R_mem\<close>


subsection \<open>Semantics\<close>

subsubsection \<open>Map Representation of Tree\<close>

text \<open>This section presents a representation of tree using the mapping from path to value,
    typically of type \<^typ>\<open>nat list \<Rightarrow> 'x\<close>.
  Basic operations include `push_map` and `pull_map` which put a sub-tree onto certain location
    and fetch a sub-tree at certain location respectively.
  It also includes scalar operation `share` which may be used to get sub-permission copies.\<close>

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
  \<comment> \<open>A tree node of children L\<close>
  where \<open>node L = (\<lambda>idx. case idx of i#idx' \<Rightarrow> (if i < length L then (L!i) idx' else 1) | _ \<Rightarrow> 1)\<close>

lemma share_node:
  \<open>share n (node L) = node (map (share n) L)\<close>
  for L :: \<open>(nat list \<Rightarrow> 'a::share_one) list\<close>
  unfolding node_def fun_eq_iff by (simp add: share_fun_def split: list.split)

lemma pull_map_node:
  \<open>pull_map (i#idx) (node L) = (if i < length L then pull_map idx (L!i) else 1)\<close>
  unfolding node_def pull_map_def fun_eq_iff by simp



subsubsection \<open>Semantics\<close>

locale agmem_sem_pre =
  aggregate where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult)
                  \<times> ('FIC_N \<Rightarrow> 'FIC::{comm_monoid_mult,no_inverse}))\<close>
+ agmem_ty where CONS_OF   = TY_CONS_OF
            and TYPE'NAME = \<open>TYPE('TY_N)\<close>
            and TYPE'REP  = \<open>TYPE('TY)\<close>
+ agmem_val where CONS_OF   = VAL_CONS_OF
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('VAL_N)\<close>
            and TYPE'REP  = \<open>TYPE('VAL::nonsepable_semigroup)\<close>
+ agmem_res where TYPE'VAL  = \<open>TYPE('VAL)\<close>
            and TYPE'TY   = \<open>TYPE('TY)\<close>
            and TYPE'NAME = \<open>TYPE('RES_N)\<close>
            and TYPE'REP  = \<open>TYPE('RES::comm_monoid_mult)\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult)
                \<times> ('FIC_N \<Rightarrow> 'FIC::{comm_monoid_mult,no_inverse})
            ) itself\<close>
fixes MemObj_Size :: \<open>'TY \<Rightarrow> nat\<close> \<comment> \<open>in size of bytes\<close>
assumes memobj_size_arr    : \<open>MemObj_Size (\<tau>Array N T) = N * MemObj_Size T\<close>
  and   memobj_size_step   : \<open>valid_idx_step T i \<Longrightarrow> MemObj_Size (idx_step_type i T) \<le> MemObj_Size T\<close>
      \<comment> \<open>It may introduce a restriction: types like zero-element tuple and array must occupy at
          least 1 byte, which may affect the performance unnecessarily. However, since zero-element
          tuple and array are so special ...
        One thing: we do not support arbitrary-length array like [0 x nat] in LLVM? TODO \<close>
assumes res_valid_mem: \<open>Resource_Validator R_mem.name = R_mem.inject ` Valid_Mem\<close>

fixes In_Mem :: \<open>('RES_N \<Rightarrow> 'RES) \<Rightarrow> 'TY segidx \<Rightarrow> bool\<close>
defines \<open>In_Mem res seg \<equiv> seg \<in> dom !!(R_mem.get res)\<close>


assumes can_eqcmp_ptr[simp]: "Can_EqCompare res (V_pointer.mk rp1) (V_pointer.mk rp2) \<longleftrightarrow>
              (memaddr.segment rp1 = memaddr.segment rp2) \<or> (rp1 = 0) \<or> (rp2 = 0) \<or>
              (In_Mem res (memaddr.segment rp1) \<and> In_Mem res (memaddr.segment rp2))"
assumes eqcmp_ptr[simp]: "EqCompare (V_pointer.mk rp1) (V_pointer.mk rp2) \<longleftrightarrow> rp1 = rp2"

assumes zero_ptr[simp]: \<open>Zero (T_pointer.mk ()) = V_pointer.mk 0\<close>


assumes idx_step_offset_size:\<open>\<I>\<D>\<X>.valid_idx_step \<I>\<D>\<X> T i
                          \<Longrightarrow> \<I>\<D>\<X>.idx_step_offset \<I>\<D>\<X> T i + MemObj_Size (\<I>\<D>\<X>.idx_step_type \<I>\<D>\<X> i T) \<le> MemObj_Size T\<close>
    and idx_step_offset_disj:\<open>\<I>\<D>\<X>.valid_idx_step \<I>\<D>\<X> T i \<Longrightarrow> \<I>\<D>\<X>.valid_idx_step \<I>\<D>\<X> T j \<Longrightarrow>
                              \<I>\<D>\<X>.idx_step_offset \<I>\<D>\<X> T i \<le> \<I>\<D>\<X>.idx_step_offset \<I>\<D>\<X> T j \<Longrightarrow>
                              \<I>\<D>\<X>.idx_step_offset \<I>\<D>\<X> T j < \<I>\<D>\<X>.idx_step_offset \<I>\<D>\<X> T i + MemObj_Size (\<I>\<D>\<X>.idx_step_type \<I>\<D>\<X> i T) \<Longrightarrow>
                              i = j\<close>

begin
abbreviation \<open>type_storable_in_mem T \<equiv> MemObj_Size T < 2^addrspace_bits\<close>

lemma Valid_Type_\<tau>Pointer[simp]:
  \<open>Valid_Type \<tau>Pointer\<close>
  unfolding Inhabited_def
  using zero_well_typ by blast

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

paragraph \<open>Index relating Mem Size\<close>

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

      have valid_idx_step_i1: \<open>\<I>\<D>\<X>.valid_idx_step \<I>\<D>\<X> (index_type base T) i1\<close>
        using prems valid_index_cat valid_index_cons obt by blast
      have valid_idx_step_i2: \<open>\<I>\<D>\<X>.valid_idx_step \<I>\<D>\<X> (index_type base T) i2\<close>
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

locale agmem_sem =
  agmem_sem_pre where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY)
                  \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                  \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult)
                  \<times> ('FIC_N \<Rightarrow> 'FIC::{comm_monoid_mult,no_inverse}))\<close>
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY)
                \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup)
                \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult)) itself\<close>

assumes WT_ptr[simp]: \<open>Well_Type \<tau>Pointer = { V_pointer.mk addr |addr. valid_rawaddr addr }\<close>

fixes Mapof_Val :: \<open>'VAL \<Rightarrow> nat list \<rightharpoonup> 'VAL\<close>
assumes Mapof_Val_inj: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> Mapof_Val Va = Mapof_Val Vb \<Longrightarrow> Va = Vb\<close>
  and   Mapof_Val_same_dom: \<open>Va \<in> Well_Type T \<Longrightarrow> Vb \<in> Well_Type T \<Longrightarrow> dom (Mapof_Val Va) = dom (Mapof_Val Vb)\<close>
  and   Mapof_not_1[simp]: \<open>Mapof_Val V \<noteq> 1\<close>
  and   Mapof_Val_pull_step: \<open>\<I>\<D>\<X>.valid_idx_step \<I>\<D>\<X> T i \<Longrightarrow> V \<in> Well_Type T
                          \<Longrightarrow> pull_map [i] (Mapof_Val V) = Mapof_Val (\<I>\<D>\<X>.idx_step_value \<I>\<D>\<X> i V)\<close>
  and   Mapof_Val_mod_step: \<open>\<I>\<D>\<X>.valid_idx_step \<I>\<D>\<X> T i \<Longrightarrow> v \<in> Well_Type T
                         \<Longrightarrow> Mapof_Val (\<I>\<D>\<X>.idx_step_mod_value \<I>\<D>\<X> i f v) = Mapof_Val v ++ push_map [i] (Mapof_Val (f (\<I>\<D>\<X>.idx_step_value \<I>\<D>\<X> i v)))\<close>
  and   Mapof_Val_tup: \<open>Mapof_Val (V_tup.mk vs) = node (map Mapof_Val vs)\<close>
  and   Mapof_Val_arr: \<open>Mapof_Val (V_array.mk (T,vs)) = node (map Mapof_Val vs)\<close>

begin

paragraph \<open>Resource Accessor\<close>

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



subsubsection \<open>Fiction\<close>


context agmem_sem
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



definition "share_mem' = 
              fiction.pointwise' (\<lambda>seg. fiction.fine (share_val_fiction (segidx.layout seg)))"

definition "share_mem = fiction_mem (fiction.defined (
              fiction.pointwise' (\<lambda>seg. fiction.fine (share_val_fiction (segidx.layout seg)))))"

lemma share_mem_def':
  \<open>share_mem = fiction_mem (fiction.defined share_mem')\<close>
  unfolding share_mem_def share_mem'_def ..

end


fiction_space (in agmem_sem) agmem_fic :: \<open>'RES_N \<Rightarrow> 'RES\<close> = std_fic +
  FIC_mem :: share_mem

(* TODO: agmem_sem should be a locale expression! ! *)


locale agmem = agmem_fic
  where TYPES = \<open>TYPE(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL::nonsepable_semigroup) \<times> ('RES_N \<Rightarrow> 'RES::comm_monoid_mult))\<close>
    and TYPE'NAME = \<open>TYPE('FIC_N)\<close>
    and TYPE'REP = \<open>TYPE('FIC::{no_inverse,comm_monoid_mult})\<close> 
+ fixes TYPES :: \<open>(('TY_N \<Rightarrow> 'TY) \<times> ('VAL_N \<Rightarrow> 'VAL) \<times> ('RES_N \<Rightarrow> 'RES) \<times> ('FIC_N \<Rightarrow> 'FIC)) itself\<close>
begin

lemma R_mem_valid_split: \<open>res \<in> Valid_Resource \<longleftrightarrow>
    R_mem.clean res \<in> Valid_Resource \<and> (\<exists>m. res R_mem.name = R_mem.inject m \<and> m \<in> Valid_Mem)\<close>
  by (subst R_mem.split, simp add: Valid_Resource_def times_fun_def res_valid_mem image_iff)
     (metis empty_iff image_iff res_valid_mem)

lemma R_mem_valid_split': \<open>NO_MATCH (R_mem.clean res') res \<Longrightarrow> res \<in> Valid_Resource \<longleftrightarrow>
    R_mem.clean res \<in> Valid_Resource \<and> (\<exists>m. res R_mem.name = R_mem.inject m \<and> m \<in> Valid_Mem)\<close>
  using R_mem_valid_split .

end


section \<open>\<phi>Type for Semantic Models\<close>

context agmem_sem begin

subsection \<open>Pointers\<close>

subsubsection \<open>Raw Pointer\<close>

definition RawPointer :: "('VAL, 'TY rawaddr) \<phi>"
  where "RawPointer x = (if valid_rawaddr x then { V_pointer.mk x } else {})"

lemma RawPointer_expn[\<phi>expns]:
  "v \<in> (p \<Ztypecolon> RawPointer) \<longleftrightarrow> v = V_pointer.mk p \<and> valid_rawaddr p"
  by (simp add: \<phi>Type_def RawPointer_def \<phi>expns)

lemma RawPointer_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited (p \<Ztypecolon> RawPointer) \<Longrightarrow> (valid_rawaddr p \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma RawPointer_zero[\<phi>reason on \<open>\<phi>Zero (T_pointer.mk ()) RawPointer ?x\<close>]:
  "\<phi>Zero \<tau>Pointer RawPointer (Null |: 0)"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns zero_prod_def zero_memaddr_def)

lemma RawPointer_eqcmp[\<phi>reason on \<open>\<phi>Equal RawPointer ?c ?eq\<close>]:
  "\<phi>Equal RawPointer (\<lambda>x y. x = 0 |: 0 \<or> y = 0 |: 0 \<or> memaddr.segment x = memaddr.segment y) (=)"
  unfolding \<phi>Equal_def by (simp add: lrep_exps \<phi>expns zero_memaddr_def) blast

lemma RawPointer_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> RawPointer) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> RawPointer) \<tau>Pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns)

subsubsection \<open>Pointer\<close>

definition Pointer :: "'TY \<Rightarrow> ('VAL, 'TY logaddr) \<phi>"
  where "Pointer TY x = (if valid_logaddr x \<and> x \<noteq> 0 \<and> logaddr_type x = TY \<and> 0 < MemObj_Size TY
                        then { V_pointer.mk (logaddr_to_raw x) }
                        else {})"

lemma Pointer_expn[\<phi>expns]:
  "v \<in> (addr \<Ztypecolon> Pointer TY) \<longleftrightarrow>
      v = V_pointer.mk (logaddr_to_raw addr) \<and> valid_logaddr addr
    \<and> addr \<noteq> 0 \<and> logaddr_type addr = TY \<and> 0 < MemObj_Size TY"
  unfolding \<phi>Type_def by (simp add: Pointer_def)

lemma Pointer_inhabited[elim!,\<phi>reason_elim!]:
  "Inhabited (addr \<Ztypecolon> Pointer TY) \<Longrightarrow>
      (valid_logaddr addr \<and> addr \<noteq> 0 \<and> logaddr_type addr = TY \<and> 0 < MemObj_Size TY \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma Pointer_eqcmp[\<phi>reason on \<open>\<phi>Equal (Pointer ?TY) ?c ?eq\<close>]:
    "\<phi>Equal (Pointer TY) (\<lambda>x y. memaddr.segment x = memaddr.segment y) (=)"
  unfolding \<phi>Equal_def
  by (simp add: \<phi>expns) (metis logaddr_to_raw_inj)

lemma Pointer_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> Pointer ?TY) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> Pointer TY) \<tau>Pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns valid_logaddr_def)

subsubsection \<open>Slice Pointer\<close>

text \<open>A limitation of the ordinary Pointer is that it cannot point to the end of an array,
  because there is no object at all at the end. To address this, there is a slice pointer which
  can range over a piece of the array including the end.\<close>

definition SlicePtr :: "'TY \<Rightarrow> ('VAL, 'TY logaddr \<times> nat \<times> nat) \<phi>"
  where "SlicePtr TY = (\<lambda>(base,i,len).
    if valid_logaddr base \<and> base \<noteq> 0 \<and> (\<exists>N. logaddr_type base = \<tau>Array N TY \<and> len \<le> N)
        \<and> 0 < MemObj_Size TY \<and> i \<le> len
    then { V_pointer.mk (logaddr_to_raw base ||+ of_nat (i * MemObj_Size TY)) }
    else {})"

lemma SlicePtr_expn[\<phi>expns]:
  \<open>v \<in> ((base, i, len) \<Ztypecolon> SlicePtr TY) \<longleftrightarrow>
      valid_logaddr base \<and> base \<noteq> 0
      \<and> (\<exists>N. logaddr_type base = \<tau>Array N TY \<and> len \<le> N)
      \<and> 0 < MemObj_Size TY \<and> i \<le> len
      \<and> v = V_pointer.mk (logaddr_to_raw base ||+ of_nat (i * MemObj_Size TY))\<close>
  unfolding SlicePtr_def \<phi>Type_def by simp blast

lemma SlicePtr_inhabited[\<phi>reason_elim!,elim!]:
  \<open>Inhabited ((base, i, len) \<Ztypecolon> SlicePtr TY)
\<Longrightarrow> (\<And>N. valid_logaddr base \<Longrightarrow> base \<noteq> 0 \<Longrightarrow> logaddr_type base = \<tau>Array N TY \<Longrightarrow> len \<le> N
          \<Longrightarrow> 0 < MemObj_Size TY \<Longrightarrow> i \<le> len \<Longrightarrow> C)
\<Longrightarrow> C\<close>
  unfolding Inhabited_def SlicePtr_expn by simp blast

lemma SlicePtr_eqcmp[\<phi>reason on \<open>\<phi>Equal (SlicePtr ?TY) ?c ?eq\<close>]:
    "\<phi>Equal (SlicePtr TY) (\<lambda>x y. fst x = fst y) (\<lambda>(_,i1,_) (_,i2,_). i1 = i2)"
  unfolding \<phi>Equal_def
  apply (clarsimp simp add: \<phi>expns word_of_nat_eq_iff take_bit_nat_def simp del: of_nat_mult)
  subgoal premises for addr i1 n1 i2 N n2 proof -
    note logaddr_storable_in_mem[OF \<open>valid_logaddr addr\<close> \<open>addr \<noteq> 0\<close>,
            unfolded \<open>logaddr_type addr = \<tau>Array N TY\<close>, unfolded memobj_size_arr]
    then have \<open>i1 * MemObj_Size TY < 2 ^ addrspace_bits\<close>
          and \<open>i2 * MemObj_Size TY < 2 ^ addrspace_bits\<close>
      by (meson \<open>i1 \<le> n1\<close> \<open>n1 \<le> N\<close> \<open>i2 \<le> n2\<close> \<open>n2 \<le> N\<close> dual_order.strict_trans2 mult_le_mono1)+
    then show ?thesis
      using \<open>0 < MemObj_Size TY\<close> by fastforce 
  qed
  done

lemma SlicePtr_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> SlicePtr ?TY) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> SlicePtr TY) \<tau>Pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (cases x, simp add: \<phi>expns valid_logaddr_def)



subsection \<open>Memory Object\<close>

definition (in agmem) Ref :: \<open>('VAL,'a) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'TY logaddr \<Zinj> 'a share) \<phi>\<close>
  where \<open>Ref T x' = (case x' of (seg |: idx) \<Zinj> (n \<Znrres> x) \<Rightarrow>
    if 0 < n \<and> valid_index (segidx.layout seg) idx then
    { FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Mapof_Val v)))))
          |v. v \<in> Well_Type (logaddr_type (seg |: idx)) \<and> v \<in> (x \<Ztypecolon> T) }
    else {})\<close>

lemma (in agmem) Ref_expn[\<phi>expns]:
  \<open>fic \<in> ((seg |: idx) \<Zinj> (n \<Znrres> v) \<Ztypecolon> Ref Identity)
    \<longleftrightarrow> 0 < n \<and> valid_index (segidx.layout seg) idx
        \<and> v \<in> Well_Type (logaddr_type (seg |: idx))
        \<and> fic = FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Mapof_Val v)))))\<close>
  unfolding Ref_def \<phi>Type_def by (simp add: Identity_def) blast

(*
definition Slice :: \<open>('VAL,'a) \<phi> \<Rightarrow> ('FIC_N \<Rightarrow> 'FIC, 'TY logaddr \<Zinj> 'a share option list) \<phi>\<close>
  where \<open>Slice T x' = (case x' of (seg |: i#idx) \<Zinj> l \<Rightarrow>
    if valid_index (segidx.layout seg) idx
     \<and> (\<exists>N TY. index_type idx (segidx.layout seg) = \<tau>Array N TY \<and> i + length l \<le> N)
    then let 
    { FIC_mem.mk (1(seg := Fine (push_map idx (share n (to_share o Mapof_Val v)))))
          |v. v \<in> Well_Type (logaddr_type (seg |: idx)) \<and> v \<in> (x \<Ztypecolon> T) }
    else {} | _ \<Rightarrow> {})\<close> *)

section \<open>Instructions & Their Specifications\<close>



subsubsection \<open>Address / Pointer\<close>

definition \<phi>M_get_logptr :: \<open>'TY \<Rightarrow> 'VAL sem_value \<Rightarrow> ('TY logaddr \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc\<close>
  where \<open>\<phi>M_get_logptr TY v F = \<phi>M_getV \<tau>Pointer V_pointer.dest v (\<lambda>p. F (rawaddr_to_log TY p))\<close>

lemma (in agmem) \<phi>M_get_logptr[\<phi>reason!]:
  \<open>(valid_logaddr addr \<Longrightarrow>
    addr \<noteq> 0 \<Longrightarrow>
    logaddr_type addr = TY \<Longrightarrow>
    0 < MemObj_Size TY \<Longrightarrow>
    \<^bold>p\<^bold>r\<^bold>o\<^bold>c F addr \<lbrace> X \<longmapsto> Y \<rbrace>) \<Longrightarrow>
   \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_logptr TY v F \<lbrace> X\<heavy_comma> addr \<Ztypecolon> Val v (Pointer TY) \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>M_get_logptr_def
  by (cases v, simp, rule \<phi>M_getV, simp add: \<phi>expns valid_logaddr_def, auto simp add: \<phi>expns)


subsection \<open>Access the Resource\<close>

subsubsection \<open>Memory Operations\<close>

definition \<phi>M_get_mem
    :: "'TY segidx \<Rightarrow> nat list \<Rightarrow> ('VAL \<Rightarrow> ('ret,'RES_N,'RES) proc) \<Rightarrow> ('ret,'RES_N,'RES) proc"
  where "\<phi>M_get_mem seg idx F =
            \<phi>M_get_res_entry R_mem.get seg (\<lambda>val.
            \<phi>M_assert (val \<in> Well_Type (segidx.layout seg)) \<ggreater> F (index_value idx val))"

definition op_load_mem :: "'TY \<Rightarrow> ('VAL, 'VAL,'RES_N,'RES) M"
  where "op_load_mem TY v =
    \<phi>M_get_logptr TY v (\<lambda>ptr.
    \<phi>M_get_mem (memaddr.segment ptr) (memaddr.index ptr) (\<lambda>x. Success (sem_value x)))"

definition op_store_mem :: "'TY \<Rightarrow> ('VAL \<times> 'VAL, unit,'RES_N,'RES) M"
  where "op_store_mem TY =
    \<phi>M_caseV (\<lambda>va vb.
    \<phi>M_get_logptr TY va (\<lambda>ptr. case ptr of (seg |: idx) \<Rightarrow>
    \<phi>M_getV TY id vb (\<lambda>v.
    \<phi>M_get_mem seg idx (\<lambda>_.
    \<phi>M_set_res_entry R_mem.updt (\<lambda>f. f(seg := map_option (index_mod_value idx (\<lambda>_. v)) (f seg)))))))"

definition op_free_mem :: "('VAL, unit,'RES_N,'RES) M"
  where "op_free_mem v =
    \<phi>M_getV \<tau>Pointer V_pointer.dest v (\<lambda>ptr. case ptr of (seg |: ofst) \<Rightarrow>
    \<phi>M_assert (ofst = 0) \<ggreater>
    \<phi>M_set_res_entry R_mem.updt (\<lambda>f. f(seg := None)))"

definition op_alloc_mem :: "'TY \<Rightarrow> ('VAL, unit,'RES_N,'RES) M"
  where "op_alloc_mem TY' v =
    \<phi>M_getV (\<tau>Int addrspace_bits) V_int.dest v (\<lambda>(_, n).
    \<phi>M_set_res_entry R_mem.updt (\<lambda>f.
    let TY = \<tau>Array n TY'
      ; addr = (@addr. f addr = None \<and> segidx.layout addr = TY)
     in f(addr := Some (Zero TY))))"

declare (in agmem) fiction_mem_\<I>[simp]

lemma (in agmem) \<phi>M_get_mem[\<phi>reason!]:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c F v \<lbrace> (seg |: idx) \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity \<longmapsto> Y \<rbrace>
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c \<phi>M_get_mem seg idx F \<lbrace> (seg |: idx) \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity \<longmapsto> Y \<rbrace>\<close>
  unfolding \<phi>Procedure_def
  apply clarify
  apply (subgoal_tac \<open>\<phi>M_get_mem seg idx F comp = F v comp\<close>)
  apply simp
  unfolding \<phi>M_get_mem_def \<phi>M_get_res_entry_def \<phi>M_get_res_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' share_mem_def
                R_mem.mult_in_dom Valid_Mem_def times_fun
                mult_strip_fine_011 times_list_def)
  subgoal premises prems for R fic res mem mem'
  proof -
    note [simp] = mult_strip_fine_011
    from \<open>mem' ## mem\<close> have t1: \<open>mem' seg ## mem seg\<close> by (simp add: sep_disj_fun) 
    show ?thesis
      using \<open>\<forall>_. \<exists>_. _ = Fine _ \<and> _ \<in> _\<close>[THEN spec[where x=seg]] t1 \<open>valid_index (segidx.layout seg) idx\<close>
        apply (auto simp add: \<open>0 < n\<close>)
      using \<open>\<forall>_ \<in> dom _. _\<close>[unfolded Ball_def, THEN spec[where x=seg]]
       apply (auto simp add: times_fun)[1]

      subgoal premises prems2 for sh' v' proof -
        have [simp]: \<open>valid_index (segidx.layout seg) idx\<close>
          by (simp add: \<open>valid_index (segidx.layout seg) idx\<close> \<open>v' \<in> Well_Type (segidx.layout seg)\<close>)
        note t2[simp] = this[THEN Mapof_Val_pull]

        have t3[simp]: \<open>pull_map idx sh' ## share n (to_share \<circ> Mapof_Val v)\<close>
          using \<open>sh' ## push_map idx _\<close> by (metis pull_map_sep_disj pull_push_map)
        have t5: \<open>index_value idx v' \<in> Well_Type (index_type idx (segidx.layout seg))\<close>
          using index_value_welltyp \<open>valid_index (segidx.layout seg) idx\<close>
                  \<open>v' \<in> Well_Type (segidx.layout seg)\<close> by blast

        let \<open>?lhs = ?rhs\<close> = \<open>to_share \<circ> Mapof_Val v' = sh' * push_map idx (share n (to_share \<circ> Mapof_Val v))\<close>
        from \<open>?lhs = ?rhs\<close> have \<open>pull_map idx ?lhs = pull_map idx ?rhs\<close> by fastforce
        note this[simplified pull_map_to_share pull_map_homo_mult pull_push_map t2]
        then have \<open>Mapof_Val (index_value idx v') = (strip_share \<circ> pull_map idx sh') ++ (Mapof_Val v)\<close>
          by (metis prems(5) prems2(6) strip_share_fun_mult strip_share_fun_share strip_share_share_funcomp(2) t2 t3)
        then have txx: \<open>index_value idx v' = v\<close>
          using Valof_Map_append Valof_Map t5
          by (metis prems(7))
        
        show ?thesis by (subst txx) standard
      qed
      done
  qed
  done

lemma (in agmem) op_load_mem:
  \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
    \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_load_mem TY raw
          \<lbrace> ptr \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> ptr \<Ztypecolon> Val raw (Pointer TY) \<longmapsto> ptr \<Zinj> n \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> \<^bold>v\<^bold>a\<^bold>l v \<Ztypecolon> Identity \<rbrace>\<close>
  unfolding Premise_def op_load_mem_def
  apply (cases ptr; simp)
  apply \<phi>reason
  apply simp
  by \<phi>reason

lemma (in agmem) op_store_mem:
   \<open>\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e v \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e u \<in> Well_Type TY
\<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c op_store_mem TY (\<phi>V_pair raw_ptr raw_u)
          \<lbrace> ptr \<Zinj> 1 \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> u \<Ztypecolon> Val raw_u Identity\<heavy_comma> ptr \<Ztypecolon> Val raw_ptr (Pointer TY)
        \<longmapsto> ptr \<Zinj> 1 \<Znrres> u \<Ztypecolon> Ref Identity\<rbrace>\<close>
  unfolding Premise_def op_store_mem_def
  apply (rule \<phi>M_caseV, rule \<phi>M_get_logptr)
  apply (cases ptr; cases raw_u; simp, \<phi>reason)
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' share_mem_def
                        R_mem.mult_in_dom times_list_def)
  subgoal premises prems for seg idx R fic res mem mem_remain'
  proof -
    show ?thesis
      using \<open>\<forall>_. \<exists>_. _ \<and> mem _ \<in> _\<close>[THEN spec[where x=seg]] \<open>mem_remain' * Fine mem \<in> Valid_Mem\<close>
      apply (auto simp add: mult_strip_fine_011 prems Valid_Mem_def times_fun
                            sep_disj_partial_map_some_none times_fine times_list_def)
      subgoal premises prems2 for fic_mR mem_R val
      proof -
        have [simp]: \<open>seg \<in> dom mem\<close> using \<open>mem seg = Some val\<close> by blast
        have [simp]: \<open>\<And>any. mem_R ## mem(seg := any)\<close> using \<open>mem_R ## _\<close> \<open>mem seg = Some val\<close>
          by (smt (verit, best) fun_upd_apply sep_disj_commuteI sep_disj_fun_def sep_disj_option(3) sep_disj_partial_map_some_none)
      have t1: \<open>dom (push_map idx (to_share \<circ> Mapof_Val u)) = dom (push_map idx (to_share \<circ> Mapof_Val v))\<close>
        by simp (meson Mapof_Val_same_dom \<open>u \<in> Well_Type _\<close> \<open>v \<in> Well_Type _\<close>)
      have t2: \<open>fic_mR ## push_map idx (to_share \<circ> Mapof_Val u)\<close>
        using total_Mapof_disjoint dom1_disjoint_sep_disj dom1_dom t1
        by (metis \<open>fic_mR ## _\<close> \<open>to_share \<circ> Mapof_Val val = _\<close>)
        
        show ?thesis
          apply (rule exI[where x=\<open>fic * FIC_mem.mk (1(seg := Fine (push_map idx (to_share \<circ> Mapof_Val u))))\<close>])
          apply (auto simp add: prems prems2 inj_image_mem_iff index_mod_value_welltyp
                                FIC_mem.interp_split' R_mem.times_fun_upd sep_disj_partial_map_upd
                                times_set_def times_fine'[symmetric] R_mem.mk_homo_mult)
          apply (fold \<open>mem_remain' = Fine mem_R\<close>,
                 fold \<open>res R_mem.name = R_mem.inject mem_remain'\<close>,
                 fold mult.assoc,
                 fold R_mem.split)
          apply (rule exI[where x=\<open>res\<close>])
          apply (rule exI[where x=\<open>R_mem.mk (Fine (mem(seg \<mapsto> index_mod_value idx (\<lambda>_. u) val)))\<close>])
          apply (simp add: prems share_mem_def )
          apply (auto simp add: mult_strip_fine_011 times_fun inj_image_mem_iff prems2 times_fine t2)
          apply (rule exI[where x =\<open>fic_mR * push_map idx (to_share \<circ> Mapof_Val u)\<close>],
              simp add: Mapof_Val_modify_fiction[of \<open>segidx.layout seg\<close> idx val v u fic_mR]
                        prems2 prems index_mod_value_welltyp)
          subgoal for x
            using \<open>\<forall>_. \<exists>y. _\<close>[THEN spec[where x=x]] apply clarsimp apply (case_tac \<open>y=1\<close>; simp)
          subgoal for y by (rule exI[where x=y], simp)
          done
        done
    qed
    done
  qed
  done

declare (in agmem) fiction_mem_\<I>[simp del]


lemma (in agmem) fiction_mem_\<I>':
  \<open> Rmem \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> (\<exists>mem. Rmem = R_mem.mk (Fine mem) \<and> mem \<in> \<I> I fic)\<close>
  unfolding fiction_mem_\<I> by clarsimp blast

lemma (in agmem) fiction_mem_\<I>'':
  \<open> Rmem R_mem.name = R_mem.inject (Fine mem)
\<Longrightarrow> Rmem \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> Rmem = R_mem.mk (Fine mem) \<and> mem \<in> \<I> I fic\<close>
  unfolding fiction_mem_\<I>' by auto

lemma (in agmem) fiction_mem_\<I>_simp:
  \<open> R_mem.mk (Fine mem) \<in> \<I> (fiction_mem (fiction.defined I)) fic
\<longleftrightarrow> mem \<in> \<I> I fic\<close>
  unfolding fiction_mem_\<I>' by simp



lemma (in agmem) share_mem_in_dom:
  \<open> mem \<in> \<I> share_mem' fic
\<Longrightarrow> seg \<in> dom1 fic
\<Longrightarrow> seg \<in> dom mem\<close>
  unfolding share_mem'_def
  by (simp add: domIff dom1_def one_fine_def)
     (smt (verit, ccfv_SIG) mem_Collect_eq option.distinct(1))


lemma (in agmem) share_mem'_mono:
  \<open> x \<in> \<I> share_mem' fx
\<Longrightarrow> y \<in> \<I> share_mem' fy
\<Longrightarrow> dom1 fx \<inter> dom1 fy = {}
\<Longrightarrow> x * y \<in> \<I> share_mem' (fx * fy)\<close>
  unfolding share_mem'_def set_eq_iff
  apply clarsimp
  subgoal premises prems for k
    using prems[THEN spec[where x=k]]
  apply (clarsimp simp add: times_fun dom1_def one_fine_def)
    subgoal for fx' fy'
      apply (cases \<open>fx' = 1\<close>; cases \<open>fy' = 1\<close>; clarsimp simp add: times_fine)
      using Mapof_not_1 to_share_funcomp_eq_1_iff by blast+
    done
  done



lemma (in agmem) share_mem'_drop_seg:
  \<open> v \<in> Well_Type (segidx.layout seg)
\<Longrightarrow> mem \<in> \<I> share_mem' (fic * 1(seg := Fine (to_share \<circ> Mapof_Val v)))
\<Longrightarrow> seg \<in> dom mem \<and> mem(seg := None) \<in> \<I> share_mem' fic\<close>
  unfolding share_mem'_def
  apply (auto simp add: times_fun)
  subgoal premises prems proof -
    show ?thesis
      using prems(2)[THEN spec[where x=seg]]
      by (clarsimp simp add: mult_strip_fine_011)
  qed
  subgoal premises prems proof -
    show ?thesis
      using prems(2)[THEN spec[where x=seg]]
      apply (clarsimp simp add: mult_strip_fine_011)  
      subgoal premises prems2 for r u proof -
        have \<open>dom r \<inter> dom (to_share o Mapof_Val v) = {}\<close>
          using total_Mapof_disjoint[where idx=\<open>[]\<close>, simplified]
                \<open>r ## (to_share \<circ> Mapof_Val v)\<close> \<open>to_share \<circ> Mapof_Val u = r * (to_share \<circ> Mapof_Val v)\<close>
          by fastforce
        moreover have \<open>dom (to_share \<circ> Mapof_Val u) = dom (to_share \<circ> Mapof_Val v)\<close>
          using Mapof_Val_same_dom
          by (metis \<open>u \<in> Well_Type (segidx.layout seg)\<close> dom_map_option_comp prems(1)) 
        moreover have \<open>dom (to_share \<circ> Mapof_Val u) = dom r \<union> dom (to_share \<circ> Mapof_Val v)\<close>
          using dom_mult by (metis prems2) 
        ultimately have \<open>dom r = {}\<close> by (metis inf_sup_absorb)
        then show ?thesis unfolding one_partial_map by blast
      qed
      done
  qed
  subgoal premises prems for x proof -
    thm prems
    show ?thesis using \<open>\<forall>_. _\<close>[THEN spec[where x=x]] \<open>x\<noteq>seg\<close> apply clarsimp
      subgoal for m by (rule exI[where x=m], simp, cases \<open>m = 1\<close>; simp)
      done
  qed
  done


lemma (in agmem) op_alloc_mem:
  \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_alloc_mem TY raw_n \<lbrace> n \<Ztypecolon> Val raw_n Size \<longmapsto> ((seg |: []) \<Zinj> 1 \<Znrres> (Zero (\<tau>Array n TY)) \<Ztypecolon> Ref Identity \<^bold>s\<^bold>u\<^bold>b\<^bold>j seg. True) \<rbrace>\<close>
  unfolding op_alloc_mem_def
  apply (cases raw_n; simp, rule \<phi>M_tail_left, rule \<phi>M_getV; simp add: \<phi>expns)
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' times_fun dom_mult
                        R_mem.mult_in_dom Valid_Mem_def mult_strip_fine_011 mult_strip_fine_001
                        fiction_mem_\<I>'' share_mem_def' times_list_def)
  subgoal premises prems for R fic res mem' mem
  proof -
    note [simp] = times_fun dom_mult
    have t0: \<open>finite (dom (mem' * mem))\<close> using prems by simp
    note t1 = Mem_freshness[OF t0, of \<open>\<tau>Array n TY\<close>, THEN someI_ex, simplified]
    let ?seg = \<open>(SOME x. mem' x = None \<and> mem x = None \<and> segidx.layout x = \<tau>Array n TY)\<close>
    have t2'[simp]: \<open>mem' ?seg = None \<and> mem ?seg = None\<close> using t1 by blast
    have t2'': \<open>?seg \<notin> dom mem\<close> by force
    have t6: \<open>\<And>any. R_mem.clean res * R_mem.mk (Fine ((mem' * mem)(?seg := any)))
                  = res * (R_mem.mk (Fine (mem * 1(?seg := any))))\<close>
      unfolding fun_upd_def fun_eq_iff
      apply (simp add: prems R_mem.inj_homo_mult[symmetric] times_fine fun_eq_iff sep_disj_fun_def)
      by (simp add: \<open>mem' ## mem\<close> sep_disj_fun)

    show ?thesis
      apply (rule exI[where x = \<open>fic * FIC_mem.mk
                  (1(?seg := Fine (to_share \<circ> Mapof_Val (V_array.mk (TY, replicate n (Zero TY))))))\<close>])
      apply (auto simp add: prems inj_image_mem_iff t1 list_all_length zero_well_typ
                            FIC_mem.interp_split' R_mem.times_fun_upd sep_disj_partial_map_upd
                            times_set_def times_fine'[symmetric] R_mem.mk_homo_mult)
       apply (rule exI[where x=\<open>?seg\<close>], rule exI[where x=fic], simp add: prems t1 list_all_length zero_well_typ)
      apply (unfold t6)
      apply (rule exI[where x=\<open>res\<close>])
      apply (rule exI[where x=\<open>R_mem.mk (Fine (mem * 1(?seg \<mapsto> V_array.mk (TY, replicate n (Zero TY)))))\<close>])
      using \<open>res \<in> \<I> INTERP (FIC_mem.clean fic)\<close>
      apply (clarsimp simp add: prems share_mem_def' fiction_mem_\<I>_simp)
      apply (rule share_mem'_mono, simp add: prems)
      apply (clarsimp simp add: share_mem'_def t1 list_all_length zero_well_typ one_fine_def)
      apply (simp add: set_eq_iff)
      using share_mem_in_dom[OF \<open>mem \<in> \<I> share_mem' (FIC_mem.get fic)\<close>]  t2'' by blast
  qed
  done


lemma (in agmem) op_free_mem:
   \<open>\<^bold>p\<^bold>r\<^bold>o\<^bold>c op_free_mem vptr \<lbrace> (seg |: []) \<Zinj> 1 \<Znrres> v \<Ztypecolon> Ref Identity\<heavy_comma> (seg |: 0) \<Ztypecolon> Val vptr RawPointer \<longmapsto> 1\<rbrace>\<close>
  unfolding op_free_mem_def
  apply (cases vptr; simp, rule \<phi>M_getV; simp add: \<phi>expns)
  unfolding \<phi>M_set_res_entry_def \<phi>Procedure_def
  apply (auto simp add: \<phi>expns FIC_mem.interp_split' R_mem_valid_split' times_fun dom_mult
                        R_mem.mult_in_dom Valid_Mem_def mult_strip_fine_011 mult_strip_fine_001
                        fiction_mem_\<I>'' share_mem_def' times_list_def)
  subgoal premises prems for R fic res memR mem
  proof -
    have t2: \<open>seg \<in> dom mem\<close>
      using share_mem'_drop_seg prems by blast 
    have t3: \<open>seg \<notin> dom memR\<close>
      by (meson domD domIff prems sep_disj_partial_map_some_none t2)
    have t1: \<open>(res * R_mem.mk (Fine mem))(R_mem.name := R_mem.inject (Fine ((memR * mem)(seg := None))))
            = res * R_mem.mk (Fine (mem(seg := None)))\<close>
      unfolding fun_eq_iff times_fun
      apply (simp add: prems R_mem.inj_homo_mult[symmetric] times_fine sep_disj_partial_map_del)
      apply (simp add: fun_upd_def fun_eq_iff times_fun)
      using domIff t3 by fastforce
    show ?thesis
      apply (rule exI[where x=fic], simp add: prems FIC_mem.interp_split' sep_disj_partial_map_del t1)
      apply (rule times_set_I, simp add: prems)
      using share_mem'_drop_seg prems
      by (metis fiction_mem_\<I>' share_mem_def')
  qed
  done



end






end