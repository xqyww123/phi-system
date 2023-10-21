theory PhiSem_Mem_Pointer
  imports PhiSem_Mem_C_Base PhiSem_Agg_Void "HOL-Library.Word"
  keywords
      "\<tribullet>" :: quasi_command
  abbrevs "+_a" = "+\<^sub>a"
      and "\<tribullet>_a"  = "\<tribullet>\<^sub>a"
      and "<Ptr>" = "\<bbbP>\<t>\<r>"
      and "<ptr>" = "\<p>\<t>\<r>"
begin

section \<open>Semantics of Pointer\<close>

subsection \<open>Type\<close>

virtual_datatype c_mem_ty =
  T_pointer :: unit

debt_axiomatization T_pointer :: \<open>unit type_entry\<close>
  where c_mem_ty_ax: \<open>c_mem_ty TY_CONS_OF T_pointer\<close>

interpretation c_mem_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_pointer using c_mem_ty_ax .

abbreviation pointer ("\<p>\<t>\<r>") where \<open>pointer \<equiv> T_pointer.mk ()\<close>

subsection \<open>Value\<close>

subsubsection \<open>Formalization Definitions\<close>

paragraph \<open>Base Representation for Logical and Physical Addresses\<close>

declare [[typedef_overloaded]]
datatype memblk = Null | MemBlk nat \<comment> \<open>id\<close> TY

setup \<open>Sign.mandatory_path "memblk"\<close>

definition \<open>layout blk = (case blk of Null \<Rightarrow> void | MemBlk _ TY \<Rightarrow> TY)\<close>

lemma layout[simp]:
  \<open>memblk.layout Null = void\<close>
  \<open>memblk.layout (MemBlk i TY) = TY\<close>
  unfolding memblk.layout_def by simp+

setup \<open>Sign.parent_path\<close>

(*TODO: rename: block, offset*)
datatype 'index memaddr = memaddr (blk: memblk) (index: 'index)
declare [[typedef_overloaded = false]]

declare memaddr.sel[iff]
hide_const (open) blk index

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
  assume \<open>\<And>blk ofs. PROP P (memaddr blk ofs)\<close>
  note this[of \<open>memaddr.blk x\<close> \<open>memaddr.index x\<close>, simplified]
  then show \<open>PROP P x\<close> .
qed


paragraph \<open>Address Space\<close>

consts addrspace_bits :: "nat" \<comment> \<open>bit width of address space, in unit of bits\<close>
specification (addrspace_bits) addrspace_bits_L0: "0 < addrspace_bits" by blast
  \<comment> \<open>We leave it unspecified and only require it is positive\<close>

typedecl size_t \<comment> \<open>size of address space\<close>

instantiation size_t :: len begin
definition [simp]: "len_of_size_t (_::size_t itself) = addrspace_bits"
instance apply standard using addrspace_bits_L0 by simp
end

abbreviation to_size_t :: \<open>nat \<Rightarrow> size_t word\<close> where \<open>to_size_t \<equiv> of_nat\<close>


paragraph \<open>Logical and Physical Addresses\<close>

type_synonym logaddr = "aggregate_path memaddr"
type_synonym rawaddr = \<open>size_t word memaddr\<close> \<comment> \<open>physical pointer having physical offset\<close>


subsubsection \<open>Algebraic Properties\<close>

instantiation memblk :: zero begin
definition [simp]: "zero_memblk = Null"
instance ..
end

instantiation memaddr :: (zero) zero begin
definition "zero_memaddr = (memaddr 0 0)"
instance ..
end

lemma memaddr_blk_zero[simp]:
  \<open>memaddr.blk 0 = Null\<close>
  unfolding zero_memaddr_def by simp

lemma memaddr_idx_zero[simp]:
  \<open>memaddr.index 0 = 0\<close>
  unfolding zero_memaddr_def by simp


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

lemma memblk_infinite[simp]:
  \<open>infinite (UNIV :: memblk set)\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>(UNIV :: memblk set)\<close>
        and f = \<open>\<lambda>n. MemBlk n undefined\<close>]
  by (meson infinite_UNIV_char_0 injI memblk.inject top_greatest)

lemma memblk_infinite_TY:
  \<open>infinite {a. memblk.layout a = TY}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{a. memblk.layout a = TY}\<close>
        and f = \<open>\<lambda>n. MemBlk n TY\<close>]
  using inj_def by fastforce

lemma Mem_freshness:
  \<open>finite (dom f) \<Longrightarrow> \<exists>k. f k = None \<and> memblk.layout k = TY\<close>
  unfolding dom_def
  by (smt (verit, del_insts) Collect_mono finite_Collect_disjI finite_subset memblk_infinite_TY)



subsubsection \<open>Validity of Mem Block and Addresses\<close>

abbreviation \<open>type_storable_in_mem T \<equiv> MemObj_Size T < 2^addrspace_bits\<close>
  \<comment> \<open>the size of type \<open>T\<close> is representable / less than the cap size of address space\<close>

definition \<open>Valid_MemBlk seg = (
    case seg of Null \<Rightarrow> True
              | MemBlk _ ty \<Rightarrow> type_storable_in_mem ty
    )\<close>

lemma Valid_MemBlk_zero[simp]: \<open>Valid_MemBlk Null\<close>
  unfolding Valid_MemBlk_def zero_memblk_def by simp

abbreviation valid_rawaddr :: \<open>rawaddr \<Rightarrow> bool\<close>
  where \<open>valid_rawaddr addr \<equiv> Valid_MemBlk (memaddr.blk addr)\<close>

definition valid_logaddr :: "logaddr \<Rightarrow> bool"
  where "valid_logaddr addr \<longleftrightarrow>
    Valid_MemBlk (memaddr.blk addr) \<and>
    (memaddr.blk addr = Null \<longrightarrow> memaddr.index addr = []) \<and>
    valid_index (memblk.layout (memaddr.blk addr)) (memaddr.index addr)"

lemma valid_rawaddr_0[simp]: \<open>valid_rawaddr 0\<close>
  by (simp add: zero_prod_def Valid_MemBlk_def zero_memaddr_def)

lemma valid_logaddr_0[simp]: \<open>valid_logaddr 0\<close>
  by (simp add: valid_logaddr_def zero_prod_def Valid_MemBlk_def zero_memaddr_def)

subsubsection \<open>Basic Operations and Properties of Addresses\<close>

paragraph \<open>Size of Memory Object\<close>

lemma MemObj_Size_LE_idx:
  \<open>valid_index T (base@idx) \<Longrightarrow> MemObj_Size (index_type (base@idx) T) \<le> MemObj_Size (index_type base T)\<close>
  by (induct base arbitrary: T idx; simp)

lemmas MemObj_Size_LE_idx_0 = MemObj_Size_LE_idx[where base = "[]", simplified]

lemma index_type_type_storable_in_mem:
  \<open>type_storable_in_mem T \<Longrightarrow> valid_index T idx \<Longrightarrow> type_storable_in_mem (index_type idx T)\<close>
  by simp


paragraph \<open>The type of the object that a pointer points to\<close>

abbreviation logaddr_type :: \<open>logaddr \<Rightarrow> TY\<close>
  where \<open>logaddr_type addr \<equiv> index_type (memaddr.index addr) (memblk.layout (memaddr.blk addr))\<close>

lemma logaddr_storable_in_mem:
  \<open>valid_logaddr addr \<Longrightarrow> type_storable_in_mem (logaddr_type addr)\<close>
  unfolding valid_logaddr_def Valid_MemBlk_def zero_memaddr_def
  by (cases addr; simp)



paragraph \<open>Relation between Logical Address and Physical Address\<close>

definition logaddr_to_raw :: \<open>logaddr \<Rightarrow> rawaddr\<close>
  where \<open>logaddr_to_raw addr =
    (case addr of memaddr seg idx \<Rightarrow> memaddr seg (to_size_t (index_offset (memblk.layout seg) idx)))\<close>

lemma logaddr_to_raw_0[simp]:
  \<open>logaddr_to_raw (memaddr blk []) = (memaddr blk 0)\<close>
  unfolding logaddr_to_raw_def by simp

lemma logaddr_to_raw_MemBlk[simp]:
  \<open>memaddr.blk (logaddr_to_raw addr) = memaddr.blk addr\<close>
  unfolding logaddr_to_raw_def by (cases addr) simp

lemma valid_logaddr_rawaddr [simp]:
  \<open>valid_logaddr addr \<Longrightarrow> valid_rawaddr (logaddr_to_raw addr)\<close>
  unfolding valid_logaddr_def by simp 

lemma index_offset_inj:
  assumes prems:
    \<open>valid_index T index1\<close>
    \<open>valid_index T index2\<close>
    \<open>index_type index2 T = index_type index1 T\<close>
    \<open>\<not> phantom_mem_semantic_type (index_type index1 T)\<close>
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
              idx_step_offset_no_overlap[where T = \<open>index_type base T\<close> and i = i1 and j = i2]
        by (smt (verit, ccfv_SIG) comp_def group_cancel.add1 idx_step_offset_no_overlap nat_add_left_cancel_less nat_le_linear obt order.strict_trans1 valid_idx_step_i1 valid_idx_step_i2)
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
     \<not> phantom_mem_semantic_type (logaddr_type addr1) \<Longrightarrow>
     logaddr_to_raw addr1 = logaddr_to_raw addr2 \<longrightarrow> addr1 = addr2\<close>
  unfolding logaddr_to_raw_def valid_logaddr_def
  by (cases addr1; cases addr2; simp; case_tac x1; case_tac x1a; simp add: phantom_mem_semantic_type_def)
      
  

definition \<open>rawaddr_to_log T raddr = (@laddr. logaddr_to_raw laddr = raddr \<and> logaddr_type laddr = T \<and> valid_logaddr laddr)\<close>

lemma rawaddr_to_log[simp]:
  \<open> valid_logaddr addr
\<Longrightarrow> \<not> phantom_mem_semantic_type (logaddr_type addr)
\<Longrightarrow> rawaddr_to_log (logaddr_type addr) (logaddr_to_raw addr) = addr\<close>
  unfolding rawaddr_to_log_def
  by (rule some_equality, simp) (metis logaddr_to_raw_inj) 

lemma logaddr_to_raw[iff]:
  \<open> (\<exists>laddr. logaddr_to_raw laddr = addr \<and> logaddr_type laddr = TY \<and> valid_logaddr laddr)
\<Longrightarrow> logaddr_to_raw (rawaddr_to_log TY addr) = addr \<and>
    logaddr_type (rawaddr_to_log TY addr) = TY \<and>
    valid_logaddr (rawaddr_to_log TY addr)\<close>
  unfolding rawaddr_to_log_def
  by (elim exE; rule someI; blast)

lemma logaddr_type__rawaddr_to_log__logaddr_type[simp]:
  \<open> valid_logaddr laddr
\<Longrightarrow> logaddr_type (rawaddr_to_log (logaddr_type laddr) (logaddr_to_raw laddr)) = logaddr_type laddr\<close>
  unfolding rawaddr_to_log_def
  by (rule someI2; simp)


subsubsection \<open>Address Arithmetic - Shift\<close>

abbreviation shift_addr :: "'idx memaddr \<Rightarrow> ('idx::monoid_add) \<Rightarrow> 'idx memaddr" (infixl "+\<^sub>a" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. delta + x) addr"

notation shift_addr (infixl "||+" 60) (*depreciated!*)

lemma mem_shift_shift[simp]: "a +\<^sub>a i +\<^sub>a j = a +\<^sub>a (j + i)" by (cases a) (simp add: add.assoc)

lemma memaddr_MemBlk_shift[simp]:
  \<open>memaddr.blk (a +\<^sub>a i) = memaddr.blk a\<close>
  by (cases a, simp)

lemma memaddr_index_shift[simp]:
  \<open>memaddr.index (a +\<^sub>a i) = i + memaddr.index a\<close>
  by (cases a, simp)

lemma mem_shift_add_cancel[simp]:
  \<open>(a +\<^sub>a i) = (a +\<^sub>a j) \<longleftrightarrow> i = j\<close>
  for i :: \<open>'a::{monoid_add,cancel_semigroup_add}\<close>
  by (cases a, simp)


subsubsection \<open>Address Arithmetic - Get Element Pointer\<close>

definition addr_gep :: "logaddr \<Rightarrow> aggregate_index \<Rightarrow> logaddr"
  where "addr_gep addr i = map_memaddr (\<lambda>idx. idx @ [i]) addr"

definition addr_geps :: "logaddr \<Rightarrow> aggregate_path \<Rightarrow> logaddr"
  where "addr_geps addr path = map_memaddr (\<lambda>idx. idx @ path) addr"

syntax "_addr_gep_" :: \<open>logaddr \<Rightarrow> \<phi>_ag_idx_ \<Rightarrow> logaddr\<close> (infixl "\<tribullet>\<^sub>a" 55)

parse_translation \<open>[
  (\<^syntax_const>\<open>_addr_gep_\<close>, fn ctxt => fn [a,x] =>
      Const(\<^const_syntax>\<open>addr_gep\<close>, dummyT) $ a $ Phi_Aggregate_Syntax.parse_index x)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>addr_gep\<close>, fn ctxt => fn [a,x] =>
      Const(\<^syntax_const>\<open>_addr_gep_\<close>, dummyT) $ a $ Phi_Aggregate_Syntax.print_index x )
]\<close>


text \<open>We can use \<^term>\<open>p \<tribullet>\<^sub>a field\<close> to access the address of the element named \<open>field\<close> in the
  object pointed by \<open>p\<close>.
  We may also use \<^term>\<open>p \<tribullet>\<^sub>a 2\<close> to access the address of the 2nd element.
  Use \<^term>\<open>p \<tribullet>\<^sub>a LOGIC_IDX(var)\<close> to access the element \<open>var\<close> which is a logical variable\<close>

text \<open>BTW, we also make the syntax for \<phi>-Type

TODO ...
\<close>


lemma addr_gep_memblk[iff]:
  \<open>memaddr.blk (addr \<tribullet>\<^sub>a LOGIC_IDX(i)) = memaddr.blk addr\<close>
  unfolding addr_gep_def by (cases addr; simp)

lemma addr_geps_memblk[iff]:
  \<open>memaddr.blk (addr_geps addr path) = memaddr.blk addr\<close>
  unfolding addr_geps_def by (cases addr; simp)

lemma addr_gep_path[iff]:
  \<open>memaddr.index (addr \<tribullet>\<^sub>a LOGIC_IDX(i)) = memaddr.index addr @ [i]\<close>
  unfolding addr_gep_def by (cases addr; simp)

lemma addr_geps_path[iff]:
  \<open>memaddr.index (addr_geps addr path) = memaddr.index addr @ path\<close>
  unfolding addr_geps_def by (cases addr; simp)

lemma addr_gep_eq[iff]:
  \<open>addra \<tribullet>\<^sub>a LOGIC_IDX(ia) = addrb \<tribullet>\<^sub>a LOGIC_IDX(ib) \<longleftrightarrow> addra = addrb \<and> ia = ib\<close>
  unfolding addr_gep_def by (cases addra; cases addrb; simp)

lemma addr_geps_simp[iff]:
  \<open>addr_geps addr (i#path) = addr_geps (addr \<tribullet>\<^sub>a LOGIC_IDX(i)) path\<close>
  unfolding addr_geps_def addr_gep_def by (cases addr; simp)

lemma addr_geps0_simp[iff]:
  \<open>addr_geps addr [] = addr\<close>
  unfolding addr_geps_def by (cases addr; simp)

lemma addr_gep_not_eq_zero[intro!, simp]:
  \<open>addr \<noteq> 0 \<Longrightarrow> addr \<tribullet>\<^sub>a LOGIC_IDX(i) \<noteq> 0\<close>
  unfolding zero_memaddr_def addr_gep_def
  by (cases addr) simp

lemma logaddr_type_gep[iff]:
  \<open>logaddr_type (addr \<tribullet>\<^sub>a LOGIC_IDX(x)) = idx_step_type x (logaddr_type addr)\<close>
  unfolding addr_gep_def by (cases addr; simp)

lemma addr_gep_valid[intro!, simp]:
  \<open> valid_idx_step (logaddr_type addr) i
\<Longrightarrow> valid_logaddr addr
\<Longrightarrow> valid_logaddr (addr \<tribullet>\<^sub>a LOGIC_IDX(i))\<close>
  unfolding valid_logaddr_def zero_memaddr_def addr_gep_def
  by (cases addr; clarsimp simp add: valid_idx_step_void)

lemma addr_geps_valid[intro!, simp]:
  \<open> valid_index (logaddr_type addr) path
\<Longrightarrow> valid_logaddr addr
\<Longrightarrow> valid_logaddr (addr_geps addr path)\<close>
  unfolding valid_logaddr_def zero_memaddr_def addr_gep_def
  by (induct path arbitrary: addr; clarsimp simp add: valid_idx_step_void;
      metis addr_geps_path addr_geps_simp addr_gep_memblk addr_gep_valid append_self_conv2 logaddr_type_gep not_Cons_self2 valid_logaddr_def)

lemma logaddr_to_raw_phantom_mem_type:
  \<open> phantom_mem_semantic_type (logaddr_type addr)
\<Longrightarrow> valid_idx_step (logaddr_type addr) i
\<Longrightarrow> logaddr_to_raw (addr \<tribullet>\<^sub>a LOGIC_IDX(i)) = logaddr_to_raw addr\<close>
  unfolding logaddr_to_raw_def addr_gep_def phantom_mem_semantic_type_def
  by (cases addr; clarsimp; insert idx_step_offset_size; fastforce)

lemma logaddr_to_raw_phantom_mem_type_gep_N:
  \<open> phantom_mem_semantic_type (logaddr_type addr)
\<Longrightarrow> valid_index (logaddr_type addr) path
\<Longrightarrow> logaddr_to_raw (addr_geps addr path) = logaddr_to_raw addr\<close>
  unfolding logaddr_to_raw_def phantom_mem_semantic_type_def addr_geps_def
  apply (induct path arbitrary: addr; clarsimp simp add: split_memaddr_meta_all)
  subgoal premises prems for a path blk ofs
    apply (simp add: prems(1)[of \<open>ofs @ [a]\<close> blk, simplified,
                  OF \<open>valid_index (idx_step_type a (index_type ofs (memblk.layout blk))) path\<close>])
    using idx_step_offset_size prems(2) by force .

subsubsection \<open>Reasoning Configuration\<close>

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> addr = addr'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> valid_logaddr addr
\<Longrightarrow> is_valid_index_of (memaddr.index addr) (memblk.layout (memaddr.blk addr')) (logaddr_type addr)\<close>
  unfolding valid_logaddr_def Premise_def is_valid_index_of_def
  by clarsimp

subsubsection \<open>Install Semantics\<close>

paragraph \<open>Install Memory\<close>

setup \<open>Sign.mandatory_path "RES"\<close>

type_synonym mem = \<open>memblk \<rightharpoonup> VAL discrete\<close>

setup \<open>Sign.parent_path\<close>

resource_space aggregate_mem =
  aggregate_mem :: \<open>{h::RES.mem. finite (dom h) \<and> (\<forall>seg \<in> dom h. h seg \<in> Some ` discrete ` Well_Type (memblk.layout seg))}\<close>
  (aggregate_mem_resource \<open>memblk.layout\<close>)
  by (standard; simp)


paragraph \<open>Install Pointer\<close>

virtual_datatype c_mem_val = V_pointer :: rawaddr

debt_axiomatization V_pointer :: \<open>rawaddr value_entry\<close>
  where c_mem_val_ax: \<open>c_mem_val VAL_CONS_OF V_pointer\<close>

interpretation c_mem_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_pointer using c_mem_val_ax .

definition In_Mem :: \<open> resource \<Rightarrow> memblk \<Rightarrow> bool \<close>
  where \<open>In_Mem res seg \<equiv> seg \<in> dom (RES.aggregate_mem.get res)\<close>

debt_axiomatization
    can_eqcmp_ptr[simp]: "Can_EqCompare res (V_pointer.mk rp1) (V_pointer.mk rp2)
           \<longleftrightarrow> (memaddr.blk rp1 = memaddr.blk rp2) \<or> (rp1 = 0) \<or> (rp2 = 0) \<or>
               (In_Mem res (memaddr.blk rp1) \<and> In_Mem res (memaddr.blk rp2))"
and eqcmp_ptr[simp]: "EqCompare (V_pointer.mk rp1) (V_pointer.mk rp2) \<longleftrightarrow> rp1 = rp2"
and zero_ptr[simp]: \<open>Zero pointer = Some (V_pointer.mk 0)\<close>
and WT_ptr[simp]: \<open>Well_Type pointer = { V_pointer.mk addr |addr. valid_rawaddr addr }\<close>

subsubsection \<open>Syntax\<close>

section \<open>\<phi>-Types for Pointer\<close>

subsection \<open>Physical Pointer\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def RawPointer :: "(VAL, rawaddr) \<phi>"
  where \<open>x \<Ztypecolon> RawPointer \<equiv> (V_pointer.mk x \<Ztypecolon> Itself \<s>\<u>\<b>\<j> valid_rawaddr x)\<close>
  deriving Basic
       and \<open>Object_Equiv RawPointer (=)\<close>
       and Functionality
       and \<open>\<phi>SemType (x \<Ztypecolon> RawPointer) pointer\<close>
       and \<open>Semantic_Zero_Val pointer RawPointer 0\<close>

lemma RawPointer_eqcmp[\<phi>reason 1200]:
  "\<phi>Equal RawPointer (\<lambda>x y. x = 0 \<or> y = 0 \<or> memaddr.blk x = memaddr.blk y) (=)"
  unfolding \<phi>Equal_def by (simp add: zero_memaddr_def; blast)


subsubsection \<open>Logical Pointer\<close>

\<phi>type_def Ptr :: "TY \<Rightarrow> (VAL, logaddr) \<phi>" ("\<bbbP>\<t>\<r> _" [999] 998)
  where \<open>x \<Ztypecolon> Ptr TY \<equiv> V_pointer.mk (logaddr_to_raw x) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> valid_logaddr x \<and> logaddr_type x = TY\<close>
  deriving Basic
       and \<open>Object_Equiv (Ptr TY) (=)\<close>
       and Functionality
       and \<open>\<phi>SemType (x \<Ztypecolon> Ptr TY) pointer\<close>

lemma Ptr_eqcmp[\<phi>reason 1000]:
    "\<phi>Equal (Ptr TY) (\<lambda>x y. memaddr.blk x = memaddr.blk y \<and> \<not> phantom_mem_semantic_type TY) (=)"
  unfolding \<phi>Equal_def
  by simp (metis logaddr_to_raw_inj)


section \<open>Semantic Operations\<close>
 
proc op_get_element_pointer[\<phi>overload \<tribullet>]:
  requires \<open>parse_eleidx_input TY input_index sem_idx spec_idx pidx reject\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and [unfolded is_valid_index_of_def, useful]: \<open>is_valid_index_of spec_idx TY TY'\<close>
       and \<open>report_unprocessed_element_index reject\<close>
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<close>
  output \<open>addr_geps addr pidx \<Ztypecolon> \<v>\<a>\<l> Ptr TY'\<close>
\<medium_left_bracket>
  $addr semantic_local_value pointer
  semantic_return \<open>
    V_pointer.mk (logaddr_to_raw (addr_geps (rawaddr_to_log TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1))) sem_idx))
      \<Turnstile> (addr_geps addr pidx \<Ztypecolon> Ptr TY')\<close>
\<medium_right_bracket> .




end