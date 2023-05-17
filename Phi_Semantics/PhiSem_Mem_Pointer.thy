theory PhiSem_Mem_Pointer
  imports PhiSem_Mem_C_Base
  abbrevs "+_a" = "+\<^sub>a"
      and "|>"  = "\<^enum>"
      and "\<^enum>_a"  = "\<^enum>\<^sub>a"
begin

section \<open>Semantics of Pointer\<close>

subsection \<open>Type\<close>

virtual_datatype c_mem_ty =
  T_pointer :: unit

debt_axiomatization T_pointer :: \<open>unit type_entry\<close>
  where c_mem_ty_ax: \<open>c_mem_ty TY_CONS_OF T_pointer\<close>

interpretation c_mem_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_pointer using c_mem_ty_ax .

abbreviation \<open>pointer \<equiv> T_pointer.mk ()\<close>

subsection \<open>Value\<close>

subsubsection \<open>Formalization Definitions\<close>

paragraph \<open>Base Representation for Logical and Physical Addresses\<close>

declare [[typedef_overloaded]]
datatype segidx = Null | Segment nat \<comment> \<open>nonce\<close> (layout: TY)

hide_const (open) layout

(*TODO: rename: block, offset*)
datatype 'index memaddr = memaddr (segment: segidx) (index: 'index) (infixl "|:" 60)
declare [[typedef_overloaded = false]]

declare memaddr.sel[iff]
hide_const (open) segment index

lemma split_memaddr_all: \<open>All P \<longleftrightarrow> (\<forall>blk ofs. P (memaddr blk ofs))\<close> by (metis memaddr.exhaust) 
lemma split_memaddr_ex : \<open>Ex P  \<longleftrightarrow> (\<exists>blk ofs. P (memaddr blk ofs))\<close> by (metis memaddr.exhaust) 
lemma split_memaddr_meta_all:
  \<open>(\<And>x. PROP P x) \<equiv> (\<And>blk ofs. PROP P (memaddr blk ofs))\<close>
proof
  fix blk ofs
  assume \<open>\<And>x. PROP P x\<close>
  then show \<open>PROP P (memaddr blk ofs)\<close> .
next
  fix x
  assume \<open>\<And>blk ofs. PROP P (blk |: ofs)\<close>
  note this[of \<open>memaddr.segment x\<close> \<open>memaddr.index x\<close>, simplified]
  then show \<open>PROP P x\<close> .
qed


paragraph \<open>Address Space\<close>

consts addrspace_bits :: "nat" \<comment> \<open>bit width of address space, in unit of bits\<close>
specification (addrspace_bits) addrspace_bits_L0: "0 < addrspace_bits" by blast
  \<comment> \<open>We leave it unspecified and only require it is positive\<close>

typedecl addr_cap \<comment> \<open>size of address space\<close>

instantiation addr_cap :: len begin
definition [simp]: "len_of_addr_cap (_::addr_cap itself) = addrspace_bits"
instance apply standard using addrspace_bits_L0 by simp
end

type_synonym size_t = \<open>addr_cap word\<close>
abbreviation to_size_t :: \<open>nat \<Rightarrow> size_t\<close> where \<open>to_size_t \<equiv> of_nat\<close>


paragraph \<open>Logical and Physical Addresses\<close>

type_synonym logaddr = "aggregate_path memaddr"
type_synonym rawaddr = \<open>size_t memaddr\<close> \<comment> \<open>physical pointer having physical offset\<close>


subsubsection \<open>Algebraic Properties\<close>

instantiation segidx :: zero begin
definition [simp]: "zero_segidx = Null"
instance ..
end

instantiation memaddr :: (zero) zero begin
definition "zero_memaddr = (0 |: 0)"
instance ..
end

paragraph \<open>Freshness\<close>

lemma infinite_UNIV_int [simp]: "infinite (UNIV::int set)"
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
  \<open>infinite (UNIV :: segidx set)\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>(UNIV :: segidx set)\<close>
        and f = \<open>\<lambda>n. Segment n undefined\<close>]
  by (meson infinite_UNIV_char_0 injI segidx.inject top_greatest)

lemma segidx_infinite_TY:
  \<open>infinite {a. segidx.layout a = TY}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{a. segidx.layout a = TY}\<close>
        and f = \<open>\<lambda>n. Segment n TY\<close>]
  using inj_def by fastforce

lemma Mem_freshness:
  \<open>finite (dom f) \<Longrightarrow> \<exists>k. f k = None \<and> segidx.layout k = TY\<close>
  unfolding dom_def
  by (smt (verit, del_insts) Collect_mono finite_Collect_disjI finite_subset segidx_infinite_TY)



subsubsection \<open>Validity of Mem Block and Addresses\<close>

abbreviation \<open>type_storable_in_mem T \<equiv> MemObj_Size T < 2^addrspace_bits\<close>
  \<comment> \<open>the size of type \<open>T\<close> is representable / less than the cap size of address space\<close>

definition \<open>Valid_Segment seg = (
    case seg of Null \<Rightarrow> True
              | Segment _ ty \<Rightarrow> type_storable_in_mem ty
    )\<close>

lemma Valid_Segment_zero[simp]: \<open>Valid_Segment Null\<close>
  unfolding Valid_Segment_def zero_segidx_def by simp

abbreviation valid_rawaddr :: \<open>rawaddr \<Rightarrow> bool\<close>
  where \<open>valid_rawaddr addr \<equiv> Valid_Segment (memaddr.segment addr)\<close>

definition valid_logaddr :: "logaddr \<Rightarrow> bool"
  where "valid_logaddr addr \<longleftrightarrow>
    Valid_Segment (memaddr.segment addr) \<and>
    (memaddr.segment addr = Null \<longrightarrow> memaddr.index addr = []) \<and>
    valid_index (segidx.layout (memaddr.segment addr)) (memaddr.index addr)"

lemma valid_rawaddr_0[simp]: \<open>valid_rawaddr (0 |: 0)\<close>
  by (simp add: zero_prod_def Valid_Segment_def zero_memaddr_def zero_segidx_def)

lemma valid_logaddr_0[simp]: \<open>valid_logaddr (0 |: [])\<close>
  by (simp add: valid_logaddr_def zero_prod_def Valid_Segment_def zero_memaddr_def zero_segidx_def)


subsubsection \<open>Basic Operations and Properties of Addresses\<close>

paragraph \<open>Size of Memory Object\<close>

lemma MemObj_Size_LE_idx:
  \<open>valid_index T (base@idx) \<Longrightarrow> MemObj_Size (index_type (base@idx) T) \<le> MemObj_Size (index_type base T)\<close>
  apply (induct base arbitrary: T idx; simp)
  subgoal for T idx apply (induct idx arbitrary: T; simp)
    using memobj_size_step order.trans by blast .

lemmas MemObj_Size_LE_idx_0 = MemObj_Size_LE_idx[where base = "[]", simplified]

lemma index_type_type_storable_in_mem:
  \<open>type_storable_in_mem T \<Longrightarrow> valid_index T idx \<Longrightarrow> type_storable_in_mem (index_type idx T)\<close>
  using MemObj_Size_LE_idx_0 order.strict_trans1 by blast 


paragraph \<open>The type of the object that a pointer points to\<close>

abbreviation logaddr_type :: \<open>logaddr \<Rightarrow> TY\<close>
  where \<open>logaddr_type addr \<equiv> index_type (memaddr.index addr) (segidx.layout (memaddr.segment addr))\<close>

lemma logaddr_storable_in_mem:
  \<open>valid_logaddr addr \<Longrightarrow> addr \<noteq> 0 \<Longrightarrow> type_storable_in_mem (logaddr_type addr)\<close>
  unfolding valid_logaddr_def Valid_Segment_def zero_memaddr_def
  apply (cases addr; simp)
  subgoal for seg idx by (cases seg; simp add: index_type_type_storable_in_mem) .

paragraph \<open>Relation between Logical Address and Physical Address\<close>

definition logaddr_to_raw :: \<open>logaddr \<Rightarrow> rawaddr\<close>
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

lemma index_offset_inj:
  assumes prems:
    \<open>valid_index T index1\<close>
    \<open>valid_index T index2\<close>
    \<open>index_type index2 T = index_type index1 T\<close>
    \<open>0 < MemObj_Size (index_type index1 T)\<close>
  shows \<open>index_offset T index1 = index_offset T index2 \<longrightarrow> index1 = index2\<close>
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




subsubsection \<open>Address Arithmetic - Shift\<close>

abbreviation shift_addr :: "'idx memaddr \<Rightarrow> ('idx::monoid_add) \<Rightarrow> 'idx memaddr" (infixl "+\<^sub>a" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. x + delta) addr"

notation shift_addr (infixl "||+" 60) (*depreciated!*)

lemma mem_shift_shift[simp]: "a +\<^sub>a i +\<^sub>a j = a +\<^sub>a (i + j)" by (cases a) (simp add: add.assoc)

lemma memaddr_segment_shift[simp]:
  \<open>memaddr.segment (a +\<^sub>a i) = memaddr.segment a\<close>
  by (cases a, simp)

lemma memaddr_index_shift[simp]:
  \<open>memaddr.index (a +\<^sub>a i) = memaddr.index a + i\<close>
  by (cases a, simp)

lemma mem_shift_add_cancel[simp]:
  \<open>(a +\<^sub>a i) = (a +\<^sub>a j) \<longleftrightarrow> i = j\<close>
  for i :: \<open>'a::{monoid_add,cancel_semigroup_add}\<close>
  by (cases a, simp)


subsubsection \<open>Address Arithmetic - Get Element Pointer\<close>

abbreviation addr_gep :: "logaddr \<Rightarrow> aggregate_index \<Rightarrow> logaddr"
  where "addr_gep addr i \<equiv> map_memaddr ((#) i) addr"

syntax "_addr_gep_" :: \<open>logaddr \<Rightarrow> \<phi>_ag_idx_ \<Rightarrow> logaddr\<close> (infixl "\<^enum>\<^sub>a" 60)

parse_translation \<open>[
  (\<^syntax_const>\<open>_addr_gep_\<close>, fn ctxt => fn [a,x] =>
      Const(\<^const_abbrev>\<open>addr_gep\<close>, dummyT) $ a $ Phi_Aggregate_Syntax.parse_index x)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>addr_gep\<close>, fn ctxt => fn [a,x] =>
      Const(\<^syntax_const>\<open>_addr_gep_\<close>, dummyT) $ a $ Phi_Aggregate_Syntax.print_index x )
]\<close>

text \<open>We can use \<^term>\<open>p \<^enum>\<^sub>a field\<close> to access the address of the element named \<open>field\<close> in the
  object pointed by \<open>p\<close>.
  We may also use \<^term>\<open>p \<^enum>\<^sub>a 2\<close> to access the address of the 2nd element.
  Use \<^term>\<open>p \<^enum>\<^sub>a LOGIC(var)\<close> to access the element \<open>var\<close> which is a logical variable\<close>

text \<open>BTW, we also make the syntax for \<phi>-Type

TODO ...
\<close>


subsubsection \<open>Install Semantics\<close>

paragraph \<open>Install Memory\<close>

setup \<open>Sign.mandatory_path "RES"\<close>

type_synonym mem = \<open>segidx \<rightharpoonup> VAL nosep\<close>

setup \<open>Sign.parent_path\<close>

resource_space aggregate_mem =
  aggregate_mem :: \<open>{h::RES.mem. finite (dom h) \<and> (\<forall>seg \<in> dom h. h seg \<in> Some ` nosep ` Well_Type (segidx.layout seg))}\<close>
  (aggregate_mem_resource \<open>segidx.layout\<close>)
  by (standard; simp)


paragraph \<open>Install Pointer\<close>

virtual_datatype c_mem_val = V_pointer :: rawaddr

debt_axiomatization V_pointer :: \<open>rawaddr value_entry\<close>
  where c_mem_val_ax: \<open>c_mem_val VAL_CONS_OF V_pointer\<close>

interpretation c_mem_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_pointer using c_mem_val_ax .

definition In_Mem :: \<open> resource \<Rightarrow> segidx \<Rightarrow> bool \<close>
  where \<open>In_Mem res seg \<equiv> seg \<in> dom (RES.aggregate_mem.get res)\<close>

debt_axiomatization
    can_eqcmp_ptr[simp]: "Can_EqCompare res (V_pointer.mk rp1) (V_pointer.mk rp2)
           \<longleftrightarrow> (memaddr.segment rp1 = memaddr.segment rp2) \<or> (rp1 = 0) \<or> (rp2 = 0) \<or>
               (In_Mem res (memaddr.segment rp1) \<and> In_Mem res (memaddr.segment rp2))"
and eqcmp_ptr[simp]: "EqCompare (V_pointer.mk rp1) (V_pointer.mk rp2) \<longleftrightarrow> rp1 = rp2"
and zero_ptr[simp]: \<open>Zero pointer = Some (V_pointer.mk 0)\<close>
and WT_ptr[simp]: \<open>Well_Type pointer = { V_pointer.mk addr |addr. valid_rawaddr addr }\<close>

subsubsection \<open>Syntax\<close>

section \<open>\<phi>-Types for Pointer\<close>

subsection \<open>Raw Pointer\<close>

definition RawPointer :: "(VAL, rawaddr) \<phi>"
  where "RawPointer x = ({ V_pointer.mk x } \<s>\<u>\<b>\<j> valid_rawaddr x)"

lemma RawPointer_expn[\<phi>expns]:
  "v \<in> (p \<Ztypecolon> RawPointer) \<longleftrightarrow> v = V_pointer.mk p \<and> valid_rawaddr p"
  by (simp add: \<phi>Type_def RawPointer_def \<phi>expns)

lemma RawPointer_inhabited[elim!, \<phi>inhabitance_rule]:
  "Inhabited (p \<Ztypecolon> RawPointer) \<Longrightarrow> (valid_rawaddr p \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: \<phi>expns)

lemma RawPointer_zero[\<phi>reason 1200]:
  "\<phi>Zero pointer RawPointer (Null |: 0)"
  unfolding \<phi>Zero_def by (simp add: \<phi>expns zero_prod_def zero_memaddr_def)

lemma RawPointer_eqcmp[\<phi>reason 1200]:
  "\<phi>Equal RawPointer (\<lambda>x y. x = 0 |: 0 \<or> y = 0 |: 0 \<or> memaddr.segment x = memaddr.segment y) (=)"
  unfolding \<phi>Equal_def by (simp add: \<phi>expns zero_memaddr_def; blast)

lemma RawPointer_semty[\<phi>reason 1200]:
  \<open>\<phi>SemType (x \<Ztypecolon> RawPointer) pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (simp add: \<phi>expns)




end