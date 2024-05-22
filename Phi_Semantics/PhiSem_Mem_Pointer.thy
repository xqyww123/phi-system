theory PhiSem_Mem_Pointer
  imports PhiSem_Mem_C_Base PhiSem_Agg_Void "HOL-Library.Word"
  keywords
      "\<tribullet>" :: quasi_command
  abbrevs "+_a" = "+\<^sub>a"
      and "<Ptr>" = "\<bbbP>\<t>\<r>"
      and "<ptr>" = "\<p>\<t>\<r>"
      and "<pointer-of>" = "\<p>\<o>\<i>\<n>\<t>\<e>\<r>-\<o>\<f>"
      and "<ptrof>" = "\<p>\<o>\<i>\<n>\<t>\<e>\<r>-\<o>\<f>"
      and "<ref>" = "\<r>\<e>\<f>"
begin

section \<open>Semantics of Pointer\<close>

subsection \<open>Type\<close>

debt_axiomatization \<p>\<o>\<i>\<n>\<t>\<e>\<r> :: TY ("\<p>\<t>\<r>")

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

declare memaddr.sel[iff, \<phi>safe_simp]
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

typedecl \<s>\<i>\<z>\<e>_\<t> \<comment> \<open>size of address space\<close>

instantiation \<s>\<i>\<z>\<e>_\<t> :: len begin
definition [iff]: "len_of_\<s>\<i>\<z>\<e>_\<t> (_::\<s>\<i>\<z>\<e>_\<t> itself) = addrspace_bits"
instance apply standard using addrspace_bits_L0 by simp
end

abbreviation to_size_t :: \<open>nat \<Rightarrow> \<s>\<i>\<z>\<e>_\<t> word\<close> where \<open>to_size_t \<equiv> of_nat\<close>

lemma unat_to_size_t[simp]:
  \<open>n < 2 ^ addrspace_bits \<Longrightarrow> unat (to_size_t n) = n\<close>
  by (simp add: of_nat_inverse)

paragraph \<open>Logical and Physical Addresses\<close>

type_synonym address = "aggregate_path memaddr" \<comment> \<open>Logical address\<close>
type_synonym rawaddr = \<open>\<s>\<i>\<z>\<e>_\<t> word memaddr\<close> \<comment> \<open>Physical pointer having physical offset\<close>


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
  \<open>finite (dom f) \<Longrightarrow> \<exists>k. f k = None \<and> memblk.layout k = TY \<and> k \<noteq> Null\<close>
  unfolding dom_def
proof (clarsimp)
  assume a1: "finite {a. \<exists>y. f a = Some y}"
  obtain bb :: "(memblk \<Rightarrow> nat) \<Rightarrow> (memblk \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
    f2: "\<forall>X28 X31 X30. bb X30 X31 X28 = (\<exists>X32. X28 = X30 X32 \<and> X31 X32)"
    by moura
  then have f3: "\<forall>f p. Collect (bb f p) = f ` Collect p"
    by auto
  obtain nn :: "memblk \<Rightarrow> nat" where
    f4: "\<forall>t n. nn (MemBlk n t) = n"
    by (metis (no_types) memblk.distinct(1) memblk.exhaust memblk.inject)
  obtain bba :: "memblk \<Rightarrow> bool" where
    f5: "\<forall>X39. bba X39 = (\<exists>X40. f X39 = Some X40)"
    by moura
  then have "finite (Collect bba)"
    using a1 by presburger
  then show ?thesis
    using f5 f4 f3 f2 by (metis (no_types) UNIV_eq_I finite_imageI infinite_UNIV_nat mem_Collect_eq memblk.distinct(1) memblk.layout(2) option.exhaust)
qed


subsubsection \<open>Semantic Types that can be stored in Memory\<close>

abbreviation \<open>type_storable_in_mem T \<equiv> MemObj_Size T < 2^addrspace_bits\<close>


subsubsection \<open>Validity of Mem Block and Addresses\<close>

definition \<open>Valid_MemBlk seg = (
    case seg of Null \<Rightarrow> True
              | MemBlk _ ty \<Rightarrow> type_storable_in_mem ty
    )\<close>

lemma Valid_MemBlk_zero[simp]: \<open>Valid_MemBlk Null\<close>
  unfolding Valid_MemBlk_def zero_memblk_def by simp

abbreviation valid_rawaddr :: \<open>rawaddr \<Rightarrow> bool\<close>
  where \<open>valid_rawaddr addr \<equiv> Valid_MemBlk (memaddr.blk addr)\<close>

definition valid_address :: "address \<Rightarrow> bool"
  where "valid_address addr \<longleftrightarrow>
    Valid_MemBlk (memaddr.blk addr) \<and>
    (memaddr.blk addr = Null \<longrightarrow> memaddr.index addr = []) \<and>
    valid_index (memblk.layout (memaddr.blk addr)) (memaddr.index addr)"

lemma valid_rawaddr_nil[simp]:
  \<open>valid_address (memaddr blk []) = Valid_MemBlk blk\<close>
  unfolding valid_address_def
  by auto

lemma valid_rawaddr_0[simp]: \<open>valid_rawaddr 0\<close>
  by (simp add: zero_prod_def Valid_MemBlk_def zero_memaddr_def)

lemma valid_address_0[simp]: \<open>valid_address 0\<close>
  by (simp add: valid_address_def zero_prod_def Valid_MemBlk_def zero_memaddr_def)

subsubsection \<open>Basic Operations and Properties of Addresses\<close>

paragraph \<open>Size of Memory Object\<close>

lemma MemObj_Size_LE_idx:
  \<open>valid_index T (base@idx) \<Longrightarrow> MemObj_Size (index_type (base@idx) T) \<le> MemObj_Size (index_type base T)\<close>
  by (induct base arbitrary: T idx; simp;
      insert add_leD2 index_offset_upper_bound_0; blast)

lemmas MemObj_Size_LE_idx_0 = MemObj_Size_LE_idx[where base = "[]", simplified]

lemma index_type_type_storable_in_mem:
  \<open>type_storable_in_mem T \<Longrightarrow> valid_index T idx \<Longrightarrow> type_storable_in_mem (index_type idx T)\<close>
  using MemObj_Size_LE_idx_0 order.strict_trans1
  by blast


paragraph \<open>The type of the object that a pointer points to\<close>

abbreviation address_type :: \<open>address \<Rightarrow> TY\<close>
  where \<open>address_type addr \<equiv> index_type (memaddr.index addr) (memblk.layout (memaddr.blk addr))\<close>

lemma address_storable_in_mem:
  \<open>valid_address addr \<Longrightarrow> type_storable_in_mem (address_type addr)\<close>
  unfolding valid_address_def Valid_MemBlk_def zero_memaddr_def
  by (cases addr; case_tac x1; simp; insert index_type_type_storable_in_mem; blast)



paragraph \<open>Relation between Logical Address and Physical Address\<close>

definition address_to_raw :: \<open>address \<Rightarrow> rawaddr\<close>
  where \<open>address_to_raw addr =
    (case addr of memaddr seg idx \<Rightarrow> memaddr seg (to_size_t (index_offset (memblk.layout seg) idx)))\<close>

lemma address_to_raw_nil[simp]:
  \<open>address_to_raw (memaddr blk []) = (memaddr blk 0)\<close>
  unfolding address_to_raw_def by simp

lemma address_to_raw_0[simp]:
  \<open>address_to_raw 0 = 0\<close>
  unfolding address_to_raw_def zero_memaddr_def by simp

lemma address_to_raw_MemBlk[simp]:
  \<open>memaddr.blk (address_to_raw addr) = memaddr.blk addr\<close>
  unfolding address_to_raw_def by (cases addr) simp

lemma valid_address_rawaddr [simp]:
  \<open>valid_address addr \<Longrightarrow> valid_rawaddr (address_to_raw addr)\<close>
  unfolding valid_address_def by simp 

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

lemma address_to_raw_inj:
    \<open>valid_address addr1 \<Longrightarrow>
     valid_address addr2 \<Longrightarrow>
     address_type addr1 = address_type addr2 \<Longrightarrow>
     \<not> phantom_mem_semantic_type (address_type addr1) \<Longrightarrow>
     address_to_raw addr1 = address_to_raw addr2 \<longrightarrow> addr1 = addr2\<close>
  unfolding address_to_raw_def valid_address_def
  by (cases addr1; cases addr2; simp; case_tac x1; case_tac x1a; simp add: phantom_mem_semantic_type_def;
      metis add_leD1 index_offset_inj index_offset_upper_bound_0 index_type_idem address_storable_in_mem memaddr.sel(1) memaddr.sel(2) memblk.layout(2) not_gr_zero order_le_less_trans phantom_mem_semantic_type_def unat_to_size_t valid_index.simps(1) valid_address_def)
      


definition \<open>rawaddr_to_log T raddr = (@laddr. address_to_raw laddr = raddr \<and> address_type laddr = T \<and> valid_address laddr)\<close>

lemma rawaddr_to_log[simp]:
  \<open> valid_address addr
\<Longrightarrow> \<not> phantom_mem_semantic_type (address_type addr)
\<Longrightarrow> rawaddr_to_log (address_type addr) (address_to_raw addr) = addr\<close>
  unfolding rawaddr_to_log_def
  by (rule some_equality, simp) (metis address_to_raw_inj) 

lemma address_to_raw[iff]:
  \<open> (\<exists>laddr. address_to_raw laddr = addr \<and> address_type laddr = TY \<and> valid_address laddr)
\<Longrightarrow> address_to_raw (rawaddr_to_log TY addr) = addr \<and>
    address_type (rawaddr_to_log TY addr) = TY \<and>
    valid_address (rawaddr_to_log TY addr)\<close>
  unfolding rawaddr_to_log_def
  by (elim exE; rule someI; blast)

lemma address_type__rawaddr_to_log__address_type[simp]:
  \<open> valid_address laddr
\<Longrightarrow> address_type (rawaddr_to_log (address_type laddr) (address_to_raw laddr)) = address_type laddr\<close>
  unfolding rawaddr_to_log_def
  by (rule someI2; simp)


lemma dereference_pointer_type:
  \<open> valid_address addr
\<Longrightarrow> c \<in> Well_Type (memblk.layout (memaddr.blk addr))
\<Longrightarrow> index_value (memaddr.index (rawaddr_to_log (address_type addr) (address_to_raw addr))) c \<in> Well_Type (address_type addr) \<close>
  by (smt (verit, del_insts) index_value_welltyp address_to_raw_MemBlk rawaddr_to_log_def someI valid_address_def)

lemma dereference_pointer_value:
  \<open> valid_address addr
\<Longrightarrow> c \<in> Well_Type (memblk.layout (memaddr.blk addr))
\<Longrightarrow> index_value (memaddr.index (rawaddr_to_log (address_type addr) (address_to_raw addr))) c
  = index_value (memaddr.index addr) c \<close>
  by (cases \<open>phantom_mem_semantic_type (address_type addr)\<close>,
      meson dereference_pointer_type index_value_welltyp phantom_mem_semantic_type_single_value valid_address_def,
      simp)

lemma dereference_pointer_update:
  \<open> valid_address addr
\<Longrightarrow> u \<in> Well_Type (memblk.layout (memaddr.blk addr))
\<Longrightarrow> v \<in> Well_Type (address_type addr)
\<Longrightarrow> index_mod_value (memaddr.index (rawaddr_to_log (address_type addr) (address_to_raw addr))) (\<lambda>_. v) u
  = index_mod_value (memaddr.index addr) (\<lambda>_. v) u \<close>
  by (cases \<open>phantom_mem_semantic_type (address_type addr)\<close>,
      metis dereference_pointer_type dereference_pointer_value index_mod_value_unchanged address_to_raw address_to_raw_MemBlk phantom_mem_semantic_type_single_value valid_address_def,
      simp)

subsubsection \<open>Address Arithmetic - Shift\<close>

abbreviation shift_addr :: "'idx memaddr \<Rightarrow> ('idx::monoid_add) \<Rightarrow> 'idx memaddr" (infixl "+\<^sub>a" 60)
  where "shift_addr addr delta \<equiv> map_memaddr (\<lambda>x. delta + x) addr"

notation shift_addr (infixl "||+" 60) (*deprecated!*)

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

definition addr_gep :: "address \<Rightarrow> aggregate_index \<Rightarrow> address"
  where "addr_gep addr i = map_memaddr (\<lambda>idx. idx @ [i]) addr"

definition addr_geps :: "address \<Rightarrow> aggregate_path \<Rightarrow> address"
  where "addr_geps addr path = map_memaddr (\<lambda>idx. idx @ path) addr"

adhoc_overloading access_to_ele_synt addr_gep

(*
syntax "_addr_gep_" :: \<open>address \<Rightarrow> \<phi>_ag_idx_ \<Rightarrow> address\<close> (infixl "\<tribullet>" 55)

parse_translation \<open>[
  (\<^syntax_const>\<open>_addr_gep_\<close>, fn ctxt => fn [a,x] =>
      Const(\<^const_syntax>\<open>addr_gep\<close>, dummyT) $ a $ Phi_Aggregate_Syntax.parse_index x)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>addr_gep\<close>, fn ctxt => fn [a,x] =>
      Const(\<^syntax_const>\<open>_addr_gep_\<close>, dummyT) $ a $ Phi_Aggregate_Syntax.print_index x )
]\<close>


text \<open>We can use \<^term>\<open>p \<tribullet> field\<close> to access the address of the element named \<open>field\<close> in the
  object pointed by \<open>p\<close>.
  We may also use \<^term>\<open>p \<tribullet> 2\<close> to access the address of the 2nd element.
  Use \<^term>\<open>p \<tribullet> LOGIC_IDX(var)\<close> to access the element \<open>var\<close> which is a logical variable\<close>
*)

lemma addr_gep_memblk[iff, \<phi>safe_simp]:
  \<open>memaddr.blk (addr \<tribullet> LOGIC_IDX(i)) = memaddr.blk addr\<close>
  unfolding addr_gep_def by (cases addr; simp)

lemma addr_geps_memblk[iff, \<phi>safe_simp]:
  \<open>memaddr.blk (addr_geps addr path) = memaddr.blk addr\<close>
  unfolding addr_geps_def by (cases addr; simp)

lemma addr_gep_path[iff, \<phi>safe_simp]:
  \<open>memaddr.index (addr \<tribullet> LOGIC_IDX(i)) = memaddr.index addr @ [i]\<close>
  unfolding addr_gep_def by (cases addr; simp)

lemma addr_geps_path[iff, \<phi>safe_simp]:
  \<open>memaddr.index (addr_geps addr path) = memaddr.index addr @ path\<close>
  unfolding addr_geps_def by (cases addr; simp)

lemma addr_gep_eq[iff, \<phi>safe_simp]:
  \<open>addra \<tribullet> LOGIC_IDX(ia) = addrb \<tribullet> LOGIC_IDX(ib) \<longleftrightarrow> addra = addrb \<and> ia = ib\<close>
  unfolding addr_gep_def by (cases addra; cases addrb; simp)

lemma addr_geps_simp[iff, \<phi>safe_simp]:
  \<open>addr_geps addr (i#path) = addr_geps (addr \<tribullet> LOGIC_IDX(i)) path\<close>
  unfolding addr_geps_def addr_gep_def by (cases addr; simp)

lemma addr_geps0_simp[iff, \<phi>safe_simp]:
  \<open>addr_geps addr [] = addr\<close>
  unfolding addr_geps_def by (cases addr; simp)

lemma addr_gep_not_eq_zero[intro!, simp, \<phi>safe_simp]:
  \<open>addr \<noteq> 0 \<Longrightarrow> addr \<tribullet> LOGIC_IDX(i) \<noteq> 0\<close>
  unfolding zero_memaddr_def addr_gep_def
  by (cases addr) simp

lemma address_type_gep[iff, \<phi>safe_simp]:
  \<open>address_type (addr \<tribullet> LOGIC_IDX(x)) = idx_step_type x (address_type addr)\<close>
  unfolding addr_gep_def by (cases addr; simp)

lemma addr_gep_valid[intro!, simp, \<phi>safe_simp]:
  \<open> valid_idx_step (address_type addr) i
\<Longrightarrow> valid_address addr
\<Longrightarrow> valid_address (addr \<tribullet> LOGIC_IDX(i))\<close>
  unfolding valid_address_def zero_memaddr_def addr_gep_def
  by (cases addr; clarsimp simp add: valid_idx_step_void)

lemma addr_geps_valid[intro!, simp, \<phi>safe_simp]:
  \<open> valid_index (address_type addr) path
\<Longrightarrow> valid_address addr
\<Longrightarrow> valid_address (addr_geps addr path)\<close>
  unfolding valid_address_def zero_memaddr_def addr_gep_def
  by (induct path arbitrary: addr; clarsimp simp add: valid_idx_step_void;
      metis addr_geps_path addr_geps_simp addr_gep_memblk addr_gep_valid append_self_conv2 address_type_gep not_Cons_self2 valid_address_def)

lemma address_to_raw_phantom_mem_type:
  \<open> phantom_mem_semantic_type (address_type addr)
\<Longrightarrow> valid_idx_step (address_type addr) i
\<Longrightarrow> address_to_raw (addr \<tribullet> LOGIC_IDX(i)) = address_to_raw addr\<close>
  unfolding address_to_raw_def addr_gep_def phantom_mem_semantic_type_def
  by (cases addr; clarsimp; insert idx_step_offset_size; fastforce)

lemma address_to_raw_phantom_mem_type_gep_N:
  \<open> phantom_mem_semantic_type (address_type addr)
\<Longrightarrow> valid_index (address_type addr) path
\<Longrightarrow> address_to_raw (addr_geps addr path) = address_to_raw addr\<close>
  unfolding address_to_raw_def phantom_mem_semantic_type_def addr_geps_def
  apply (induct path arbitrary: addr; clarsimp simp add: split_memaddr_meta_all)
  subgoal premises prems for a path blk ofs proof -
    have t1: \<open>MemObj_Size (index_type (ofs @ [a]) (memblk.layout blk)) = 0\<close>
      using phantom_mem_semantic_type_def phantom_mem_semantic_type_element prems(2) prems(3) by force
    have t2: \<open>valid_index (index_type (ofs @ [a]) (memblk.layout blk)) path\<close>
      by (simp add: prems(4))
    thm prems(1)[of \<open>ofs @ [a]\<close> blk, OF t1 t2]
    show ?thesis
      by (insert prems(1)[of \<open>ofs @ [a]\<close> blk, OF t1 t2]
                 idx_step_offset_size prems(2) prems(3), fastforce)
  qed .


subsubsection \<open>Reasoning Configuration\<close>

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> addr = addr'
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> valid_address addr
\<Longrightarrow> is_valid_index_of (memaddr.index addr) (memblk.layout (memaddr.blk addr')) (address_type addr)\<close>
  unfolding valid_address_def Premise_def is_valid_index_of_def
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

(*
virtual_datatype c_mem_val = V_pointer :: rawaddr

debt_axiomatization V_pointer :: \<open>rawaddr value_entry\<close>
  where c_mem_val_ax: \<open>c_mem_val VAL_CONS_OF V_pointer\<close>

interpretation c_mem_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_pointer using c_mem_val_ax .
*)

definition In_Mem :: \<open> resource \<Rightarrow> memblk \<Rightarrow> bool \<close>
  where \<open>In_Mem res seg \<equiv> seg \<in> dom (RES.aggregate_mem.get res)\<close>

  
debt_axiomatization sem_mk_pointer   :: \<open>rawaddr \<Rightarrow> VAL\<close>
                and sem_dest_pointer :: \<open>VAL \<Rightarrow> rawaddr\<close>
where sem_dest_mk_pointer[simp]:
        \<open>sem_dest_pointer (sem_mk_pointer raw) = raw\<close>
  and can_eqcmp_ptr[simp]: 
        \<open>Can_EqCompare res (sem_mk_pointer rp1) (sem_mk_pointer rp2)
           \<longleftrightarrow> (memaddr.blk rp1 = memaddr.blk rp2) \<or> (rp1 = 0) \<or> (rp2 = 0) \<or>
               (In_Mem res (memaddr.blk rp1) \<and> In_Mem res (memaddr.blk rp2))\<close>
  and eqcmp_ptr[simp]: "EqCompare (sem_mk_pointer rp1) (sem_mk_pointer rp2) \<longleftrightarrow> rp1 = rp2"
  and zero_ptr[simp]: \<open>Zero \<p>\<t>\<r> = Some (sem_mk_pointer 0)\<close>
  and WT_ptr[simp]: \<open>Well_Type \<p>\<t>\<r> = { sem_mk_pointer addr |addr. valid_rawaddr addr }\<close>


subsubsection \<open>Syntax\<close>

section \<open>\<phi>-Types for Pointer\<close>

subsection \<open>Physical Pointer\<close>

\<phi>type_def RawPointer :: "(VAL, rawaddr) \<phi>"
  where \<open>x \<Ztypecolon> RawPointer \<equiv> (sem_mk_pointer x \<Ztypecolon> Itself \<s>\<u>\<b>\<j> valid_rawaddr x)\<close>
  deriving Basic
       and \<open>Object_Equiv RawPointer (=)\<close>
       and Functionality
       and \<open>Semantic_Type RawPointer \<p>\<t>\<r>\<close>
       and \<open>Semantic_Zero_Val \<p>\<t>\<r> RawPointer 0\<close>

lemma RawPointer_eqcmp[\<phi>reason 1200]:
  "\<phi>Equal RawPointer (\<lambda>x y. x = 0 \<or> y = 0 \<or> memaddr.blk x = memaddr.blk y) (=)"
  unfolding \<phi>Equal_def by (simp add: zero_memaddr_def; blast)


subsection \<open>Standard Logical Pointer\<close>
  \<comment> \<open>which always points to the beginning address of a component of a valid memory object.
      cannot point to the end of an allocation block, which is its limitation.
      only has GEP (Get-Element-Pointer) but no shift arithmetic (+ and -) \<close>

\<phi>type_def Ptr :: "TY \<Rightarrow> (VAL, address) \<phi>" ("\<bbbP>\<t>\<r> _" [900] 899)
  where \<open>x \<Ztypecolon> Ptr TY \<equiv> sem_mk_pointer (address_to_raw x) \<Ztypecolon> Itself \<s>\<u>\<b>\<j> valid_address x \<and> (x = 0 \<or> address_type x = TY)\<close>
  deriving Basic
       and \<open>Object_Equiv (Ptr TY) (=)\<close>
       and Functionality
       and \<open>Semantic_Type (Ptr TY) \<p>\<t>\<r>\<close>
       and \<open>Semantic_Zero_Val \<p>\<t>\<r> (Ptr TY) 0\<close>


lemma Ptr_eqcmp[\<phi>reason 1000]:
    "\<phi>Equal (Ptr TY) (\<lambda>x y. x = 0 \<or> y = 0 \<or> memaddr.blk x = memaddr.blk y \<and> \<not> phantom_mem_semantic_type TY) (=)"
  unfolding \<phi>Equal_def
  by simp (metis address_to_raw_0 address_to_raw_MemBlk address_to_raw_inj memaddr.expand memaddr_blk_zero valid_address_def zero_list_def zero_memaddr_def)  


lemma Ptr_to_Raw_Pointer[\<phi>reason %ToA_cut]:
  \<open> Threshold_Cost 9
\<Longrightarrow> x \<Ztypecolon> \<bbbP>\<t>\<r> TY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> address_to_raw x \<Ztypecolon> RawPointer \<w>\<i>\<t>\<h> valid_address x \<and> (x = 0 \<or> address_type x = TY) \<close>
  \<medium_left_bracket>
     to \<open>OPEN _ _\<close>
     \<open>address_to_raw x \<Ztypecolon> MAKE _ RawPointer\<close> certified by auto_sledgehammer
  \<medium_right_bracket> .

lemma [\<phi>reason %cutting ]:
  \<open>x \<Ztypecolon> \<bbbP>\<t>\<r> TY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> RawPointer \<s>\<u>\<b>\<j> y. y = address_to_raw x \<and> valid_address x \<and> (x = 0 \<or> address_type x = TY) @tag to RawPointer\<close>
  \<medium_left_bracket> \<medium_right_bracket> .

lemma Raw_Pointer_to_Ptr[\<phi>reason %ToA_cut]:
  \<open> Threshold_Cost 9
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> address_to_raw y = x \<and> valid_address y \<and> (y = 0 \<or> address_type y = TY)
\<Longrightarrow> x \<Ztypecolon> RawPointer \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<bbbP>\<t>\<r> TY \<close>
  \<medium_left_bracket>
    to \<open>OPEN _ _\<close>
    \<open>y \<Ztypecolon> MAKE _ (\<bbbP>\<t>\<r> TY)\<close>
  \<medium_right_bracket> .

lemma [\<phi>reason %cutting ]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> address_to_raw y = x \<and> valid_address y \<and> (y = 0 \<or> address_type y = TY)
\<Longrightarrow> x \<Ztypecolon> RawPointer \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> a \<Ztypecolon> \<bbbP>\<t>\<r> TY \<s>\<u>\<b>\<j> a. a = y  @tag to (\<bbbP>\<t>\<r> TY)\<close>
  \<medium_left_bracket> \<medium_right_bracket> .




section \<open>Primitive Instructions\<close>


subsection \<open>GEP\<close>

proc op_get_element_pointer[\<phi>overload \<tribullet> 30]:
  requires \<open>parse_eleidx_input TY input_index sem_idx spec_idx reject\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and [unfolded is_valid_index_of_def, useful]: \<open>is_valid_index_of spec_idx TY TY'\<close>
       and \<open>report_unprocessed_element_index reject\<close>
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>addr_geps addr spec_idx \<Ztypecolon> \<v>\<a>\<l> Ptr TY'\<close>
\<medium_left_bracket>
  $addr semantic_local_value \<p>\<t>\<r>
  semantic_return \<open>
    sem_mk_pointer (address_to_raw (addr_geps (rawaddr_to_log TY (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1))) sem_idx))
        \<Turnstile> (addr_geps addr spec_idx \<Ztypecolon> Ptr TY')\<close>
\<medium_right_bracket> .


lemma [\<phi>reason %\<phi>synthesis_literal]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 \<Ztypecolon> \<v>\<a>\<l>[semantic_literal (sem_mk_pointer 0)] \<bbbP>\<t>\<r> TY \<r>\<e>\<m>\<a>\<i>\<n>\<s> X @tag synthesis\<close>
  for X :: assn
  \<medium_left_bracket>
    semantic_literal \<open>sem_mk_pointer 0 \<Turnstile> (0 \<Ztypecolon> \<bbbP>\<t>\<r> TY)\<close>
    certified by auto_sledgehammer
  \<medium_right_bracket> .


proc NULL:
  input  Void
  output \<open>0 \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> TY\<close>
\<medium_left_bracket>
  \<open>0 \<Ztypecolon> \<bbbP>\<t>\<r> TY\<close>
\<medium_right_bracket> .


section \<open>Reasoning Configuration\<close>

subsection \<open>common_multiplicator of path\<close>

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) (memaddr.index (memaddr _ _)) _ _\<close>]:
  \<open> common_multiplicator_2 (@) pa pb pc
\<Longrightarrow> common_multiplicator_2 (@) (memaddr.index (memaddr a pa)) pb pc \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) _ (memaddr.index (memaddr _ _)) _\<close>]:
  \<open> common_multiplicator_2 (@) pa pb pc
\<Longrightarrow> common_multiplicator_2 (@) pa (memaddr.index (memaddr a pb)) pc \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list for \<open>common_multiplicator_2 (@) _ _ (memaddr.index (memaddr _ _))\<close>]:
  \<open> common_multiplicator_2 (@) pa pb pc
\<Longrightarrow> common_multiplicator_2 (@) pa pb (memaddr.index (memaddr a pc)) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) _ _ (memaddr.index (_ \<tribullet> LOGIC_IDX(_)))\<close>]:
  \<open> common_multiplicator_2 (@) a b (memaddr.index c @ [i])
\<Longrightarrow> common_multiplicator_2 (@) a b (memaddr.index (c \<tribullet> LOGIC_IDX(i))) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) _ _ (memaddr.index (_ \<tribullet> LOGIC_IDX(_)) @ _)\<close>]:
  \<open> common_multiplicator_2 (@) a b (memaddr.index c @ [i] @ cr)
\<Longrightarrow> common_multiplicator_2 (@) a b (memaddr.index (c \<tribullet> LOGIC_IDX(i)) @ cr) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) _ (memaddr.index (_ \<tribullet> LOGIC_IDX(_))) _\<close>]:
  \<open> common_multiplicator_2 (@) a (memaddr.index b @ [i]) c
\<Longrightarrow> common_multiplicator_2 (@) a (memaddr.index (b \<tribullet> LOGIC_IDX(i))) c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) _ (memaddr.index (_ \<tribullet> LOGIC_IDX(_)) @ _) _\<close>]:
  \<open> common_multiplicator_2 (@) a (memaddr.index b @ [i] @ br) c
\<Longrightarrow> common_multiplicator_2 (@) a (memaddr.index (b \<tribullet> LOGIC_IDX(i)) @ br) c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) (memaddr.index (_ \<tribullet> LOGIC_IDX(_))) _ _\<close>]:
  \<open> common_multiplicator_2 (@) (memaddr.index a @ [i]) b c
\<Longrightarrow> common_multiplicator_2 (@) (memaddr.index (a \<tribullet> LOGIC_IDX(i))) b c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) (memaddr.index (_ \<tribullet> LOGIC_IDX(_)) @ _) _ _ \<close>]:
  \<open> common_multiplicator_2 (@) (memaddr.index a @ [i] @ ar) b c
\<Longrightarrow> common_multiplicator_2 (@) (memaddr.index (a \<tribullet> LOGIC_IDX(i)) @ ar) b c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp



lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) _ _ (memaddr.index (addr_geps _ _))\<close>]:
  \<open> common_multiplicator_2 (@) a b (memaddr.index c @ i)
\<Longrightarrow> common_multiplicator_2 (@) a b (memaddr.index (addr_geps c i)) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) _ _ (memaddr.index (addr_geps _ _) @ _)\<close>]:
  \<open> common_multiplicator_2 (@) a b (memaddr.index c @ i @ cr)
\<Longrightarrow> common_multiplicator_2 (@) a b (memaddr.index (addr_geps c i) @ cr) \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) _ (memaddr.index (addr_geps _ _)) _\<close>]:
  \<open> common_multiplicator_2 (@) a (memaddr.index b @ i) c
\<Longrightarrow> common_multiplicator_2 (@) a (memaddr.index (addr_geps b i)) c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) _ (memaddr.index (addr_geps _ _) @ _) _\<close>]:
  \<open> common_multiplicator_2 (@) a (memaddr.index b @ i @ br) c
\<Longrightarrow> common_multiplicator_2 (@) a (memaddr.index (addr_geps b i) @ br) c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) (memaddr.index (addr_geps _ _)) _ _\<close>]:
  \<open> common_multiplicator_2 (@) (memaddr.index a @ i) b c
\<Longrightarrow> common_multiplicator_2 (@) (memaddr.index (addr_geps a i)) b c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp

lemma [\<phi>reason %common_multiplicator_2_list
           for \<open>common_multiplicator_2 (@) (memaddr.index (addr_geps _ _) @ _) _ _ \<close>]:
  \<open> common_multiplicator_2 (@) (memaddr.index a @ i @ ar) b c
\<Longrightarrow> common_multiplicator_2 (@) (memaddr.index (addr_geps a i) @ ar) b c \<close>
  unfolding common_multiplicator_2_def
  by clarsimp




subsection \<open>Abstracting Raw Address Offset\<close>

definition abstract_address_offset :: \<open>address \<Rightarrow> TY \<Rightarrow> TY \<Rightarrow> nat \<Rightarrow> address \<Rightarrow> bool\<close>
  where \<open>abstract_address_offset addr TY TY' n addr' \<longleftrightarrow>
    valid_address addr \<and> address_type addr = TY \<longrightarrow>
   (valid_address addr' \<and>
    address_to_raw addr ||+ of_nat (MemObj_Size TY * n) = address_to_raw addr' \<and>
    address_type addr' = TY') \<close>


subsection \<open>Syntax of and auto deriviation for \<open>\<p>\<o>\<i>\<n>\<t>\<e>\<r>-\<o>\<f>\<close>\<close>

consts pointer_of_syntax :: \<open>('c,'x) \<phi> \<Rightarrow> VAL assertion\<close> ("\<p>\<o>\<i>\<n>\<t>\<e>\<r>-\<o>\<f>")
       pointer_val_of_syntax :: \<open>VAL \<phi>arg \<Rightarrow> ('c,'x) \<phi> \<Rightarrow> 'm::one assertion\<close>

syntax "_ref_" :: \<open>logic \<Rightarrow> logic\<close> ("\<r>\<e>\<f> _" [22] 21)

translations
  "\<v>\<a>\<l> \<p>\<o>\<i>\<n>\<t>\<e>\<r>-\<o>\<f> T" => "CONST pointer_val_of_syntax (CONST anonymous) T"
  "x \<Ztypecolon> \<r>\<e>\<f> T\<heavy_comma> C"    => "CONST pointer_val_of_syntax (CONST anonymous) T\<heavy_comma> x \<Ztypecolon> T\<heavy_comma> C"
  "x \<Ztypecolon> \<r>\<e>\<f> T"       => "CONST pointer_val_of_syntax (CONST anonymous) T\<heavy_comma> x \<Ztypecolon> T"

definition Pointer_Of :: \<open>('c,'x) \<phi> \<Rightarrow> 'v assertion \<Rightarrow> bool\<close>
                          ("\<p>\<o>\<i>\<n>\<t>\<e>\<r>-\<o>\<f> _ \<i>\<s> _" [11,11] 10)
  where \<open>Pointer_Of T assn \<equiv> True\<close>

definition Derive_Pointer_Of :: \<open>'assertion_or_\<phi>type::{} \<Rightarrow> VAL assertion option \<Rightarrow> bool\<close>
  where \<open>Derive_Pointer_Of assn ptr \<equiv> True\<close>

ML_file \<open>library/reasoning/pointer_of.ML\<close>

\<phi>property_deriver Pointer_Of 100 for ( \<open>Pointer_Of _ _\<close> ) = \<open> pointer_of_deriver \<close>


subsubsection \<open>Reasoning Rules\<close>

\<phi>reasoner_group deriving_pointer = (100, [1,3000])
      \<open>Infer the pointer assertion from a given \<phi>-type\<close>
  and deriving_pointer_cut = (1000, [1000,1030]) in deriving_pointer \<open>cutting\<close>
  and deriving_pointer_fallback = (5, [5,10]) in deriving_pointer \<open>fallback\<close>

declare [[ \<phi>reason_default_pattern
    \<open>Derive_Pointer_Of ?X _\<close> \<Rightarrow> \<open>Derive_Pointer_Of ?X _\<close> (100)
]]

definition \<A>merge_option :: \<open>VAL assertion option \<Rightarrow> VAL assertion option \<Rightarrow> VAL assertion option \<Rightarrow> bool\<close>
  where \<open>\<A>merge_option _ _ _ \<equiv> True\<close>

lemma [\<phi>reason %cutting+5 for \<open>\<A>merge_option (Some _) _ _\<close>]:
  \<open> \<A>merge_option (Some p) any (Some p) \<close>
  unfolding \<A>merge_option_def ..

lemma [\<phi>reason %cutting+5 for \<open>\<A>merge_option _ (Some _) _\<close>]:
  \<open> \<A>merge_option any (Some p) (Some p) \<close>
  unfolding \<A>merge_option_def ..

lemma [\<phi>reason %cutting+10 for \<open>\<A>merge_option (Some _) (Some _) _\<close>]:
  \<open> \<g>\<u>\<a>\<r>\<d> p = p'
\<Longrightarrow> \<A>merge_option (Some p) (Some p') (Some p) \<close>
  unfolding \<A>merge_option_def \<r>Guard_def ..

lemma [\<phi>reason %cutting for \<open>\<A>merge_option _ _ _\<close>]:
  \<open> \<A>merge_option any\<^sub>1 any\<^sub>2 None \<close>
  unfolding \<A>merge_option_def ..

lemma [\<phi>reason default %deriving_pointer_fallback]:
  \<open> Derive_Pointer_Of A None \<close>
  unfolding Derive_Pointer_Of_def ..

lemma [\<phi>reason %deriving_pointer_cut]:
  \<open> Derive_Pointer_Of A ptr\<^sub>A
\<Longrightarrow> Derive_Pointer_Of B ptr\<^sub>B
\<Longrightarrow> \<A>merge_option ptr\<^sub>A ptr\<^sub>B ptr
\<Longrightarrow> Derive_Pointer_Of (PROP A &&& PROP B) ptr \<close>
  unfolding Derive_Pointer_Of_def ..

lemma [\<phi>reason %deriving_pointer_cut]:
  \<open> Derive_Pointer_Of A ptr
\<Longrightarrow> Derive_Pointer_Of (TERM A) ptr \<close>
  unfolding Derive_Pointer_Of_def ..

lemma [\<phi>reason %deriving_pointer_cut]:
  \<open> Derive_Pointer_Of A ptr\<^sub>A
\<Longrightarrow> Derive_Pointer_Of B ptr\<^sub>B
\<Longrightarrow> \<A>merge_option ptr\<^sub>A ptr\<^sub>B ptr
\<Longrightarrow> Derive_Pointer_Of (A * B) ptr \<close>
  unfolding Derive_Pointer_Of_def ..

lemma [\<phi>reason %deriving_pointer_cut]:
  \<open> Derive_Pointer_Of A ptr\<^sub>A
\<Longrightarrow> Derive_Pointer_Of B ptr\<^sub>B
\<Longrightarrow> \<A>merge_option ptr\<^sub>A ptr\<^sub>B ptr
\<Longrightarrow> Derive_Pointer_Of (A + B) ptr \<close>
  unfolding Derive_Pointer_Of_def ..

lemma [\<phi>reason %deriving_pointer_cut]:
  \<open> Derive_Pointer_Of A ptr\<^sub>A
\<Longrightarrow> Derive_Pointer_Of B ptr\<^sub>B
\<Longrightarrow> \<A>merge_option ptr\<^sub>A ptr\<^sub>B ptr
\<Longrightarrow> Derive_Pointer_Of (A \<and>\<^sub>B\<^sub>I B) ptr \<close>
  unfolding Derive_Pointer_Of_def ..

lemma [\<phi>reason %deriving_pointer_cut]:
  \<open> (\<And>x. Derive_Pointer_Of (A x) ptr)
\<Longrightarrow> Derive_Pointer_Of (\<exists>*x. A x) ptr \<close>
  unfolding Derive_Pointer_Of_def ..

lemma [\<phi>reason %deriving_pointer_cut]:
  \<open> Derive_Pointer_Of A ptr
\<Longrightarrow> Derive_Pointer_Of (A \<s>\<u>\<b>\<j> P) ptr \<close>
  unfolding Derive_Pointer_Of_def ..





end