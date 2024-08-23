theory PhSm_Addr
  imports PhiSem_Void
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

datatype 'index gen_addr = addr (blk: block) (index: 'index)
  \<comment> \<open>generic address\<close>
declare [[typedef_overloaded = false]]

declare gen_addr.sel[iff, \<phi>safe_simp]
hide_const (open) blk index

lemma split_memaddr_all: \<open>All P \<longleftrightarrow> (\<forall>blk ofs. P (addr blk ofs))\<close> by (metis gen_addr.exhaust) 
lemma split_memaddr_ex : \<open>Ex P  \<longleftrightarrow> (\<exists>blk ofs. P (addr blk ofs))\<close> by (metis gen_addr.exhaust) 
lemma split_memaddr_meta_all:
  \<open>(\<And>x. PROP P x) \<equiv> (\<And>blk ofs. PROP P (addr blk ofs))\<close>
proof
  fix blk ofs
  assume \<open>\<And>x. PROP P x\<close>
  then show \<open>PROP P (addr blk ofs)\<close> .
next
  fix x
  assume \<open>\<And>blk ofs. PROP P (addr blk ofs)\<close>
  note this[of \<open>gen_addr.blk x\<close> \<open>gen_addr.index x\<close>, simplified]
  then show \<open>PROP P x\<close> .
qed


end