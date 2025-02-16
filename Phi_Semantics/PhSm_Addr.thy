theory PhSm_Addr
  imports PhiSem_Agg_Void
begin

declare [[typedef_overloaded]]
datatype block = Null | Block nat TY

setup \<open>Sign.mandatory_path "block"\<close>

definition \<open>layout blk = (case blk of Null \<Rightarrow> \<v>\<o>\<i>\<d> | Block _ TY \<Rightarrow> TY)\<close>

lemma layout[simp]:
  \<open>block.layout Null = \<v>\<o>\<i>\<d>\<close>
  \<open>block.layout (Block i TY) = TY\<close>
  unfolding block.layout_def by simp+

setup \<open>Sign.parent_path\<close>

(*TODO: rename: block, offset*)
datatype 'index addr = Addr (blk: block) (offset: 'index)
declare [[typedef_overloaded = false]]

declare addr.sel[iff, \<phi>safe_simp]
hide_const (open) blk index

lemma split_memaddr_all: \<open>All P \<longleftrightarrow> (\<forall>blk ofs. P (Addr blk ofs))\<close> by (metis addr.exhaust) 
lemma split_memaddr_ex : \<open>Ex P  \<longleftrightarrow> (\<exists>blk ofs. P (Addr blk ofs))\<close> by (metis addr.exhaust) 
lemma split_memaddr_meta_all:
  \<open>(\<And>x. PROP P x) \<equiv> (\<And>blk ofs. PROP P (Addr blk ofs))\<close>
proof
  fix blk ofs
  assume \<open>\<And>x. PROP P x\<close>
  then show \<open>PROP P (Addr blk ofs)\<close> .
next
  fix x
  assume \<open>\<And>blk ofs. PROP P (Addr blk ofs)\<close>
  note this[of \<open>addr.blk x\<close> \<open>addr.offset x\<close>, simplified]
  then show \<open>PROP P x\<close> .
qed

type_synonym address = "aggregate_path addr" \<comment> \<open>Logical address\<close>

subsubsection \<open>Algebraic Properties\<close>

instantiation block :: zero begin
definition [simp]: "zero_block = Null"
instance ..
end

instantiation addr :: (zero) zero begin
definition "zero_addr = (Addr 0 0)"
instance ..
end

lemma memaddr_blk_zero[simp]:
  \<open>addr.blk 0 = Null\<close>
  unfolding zero_addr_def by simp

lemma memaddr_ofs_zero[simp]:
  \<open>addr.offset 0 = 0\<close>
  unfolding zero_addr_def by simp

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

lemma block_infinite[simp]:
  \<open>infinite (UNIV :: block set)\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>(UNIV :: block set)\<close>
        and f = \<open>\<lambda>n. Block n undefined\<close>]
  by (meson infinite_UNIV_char_0 injI block.inject top_greatest)

lemma block_infinite_TY:
  \<open>infinite {a. block.layout a = TY}\<close>
  using inj_on_finite[where A = \<open>UNIV::nat set\<close> and B = \<open>{a. block.layout a = TY}\<close>
        and f = \<open>\<lambda>n. Block n TY\<close>]
  using inj_def by fastforce

subsection \<open>Address Type\<close>

definition address_type :: \<open>address \<Rightarrow> TY\<close>
  where \<open>address_type addr \<equiv> index_type (addr.offset addr) (block.layout (addr.blk addr))\<close>

adhoc_overloading Type_Of_syntax address_type



end