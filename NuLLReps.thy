theory NuLLReps
  imports NuPrime  "HOL-Library.Word"
  abbrevs "<own>" = "\<left_fish_tail>"
    and "<none>" = "\<down_fish_tail>"
    and "<object>" = "\<R_arr_tail>"
    and "<pointer>"  = "\<TeardropAsterisk>"
begin   

text \<open>Semantic data representations\<close>

declare pair_forall[lrep_exps] pair_exists[lrep_exps]

section \<open>Preliminary notions\<close>

class field = lrep \<comment> \<open>a field in the record tuple\<close>
class field_list = lrep

section \<open>Memory address\<close>

datatype ('spc::len0) memptr = memptr memaddr  \<comment> \<open>'spc : address space\<close>

(* consts segment_len :: "identifier \<Rightarrow> nat" \<comment> \<open>in unit of the number of elements\<close> *)
consts segment_llty :: "msegment \<Rightarrow> llty" \<comment> \<open>type of the element in the segment\<close>
abbreviation "memaddr_llty adr \<equiv> segment_llty (segment_of_addr adr)"
consts segment_space :: "memaddr \<Rightarrow> nat" \<comment> \<open>LLVM address space of the segment\<close>
consts adrspace_capacity :: "nat \<Rightarrow> nat" \<comment> \<open>in unit of bits\<close>
specification (adrspace_capacity) adrspace_capacity_L0[intro]: "0 < adrspace_capacity spc" by auto
(* specification (segment_len) segment_len_max: "segment_len seg < (2::nat) ^ adrspace_capacity (segment_space seg)"
  proof show "\<forall>seg. (\<lambda>x. 0) seg < (2::nat) ^ adrspace_capacity (segment_space seg)" by auto qed *)
(* specification (segment_len) segment_len_max: "segment_len seg * size_of (segment_llty seg) < adrspace_capacity (segment_space seg)"
  proof show "\<forall>seg. (\<lambda>x. 0) seg * size_of (segment_llty seg) < adrspace_capacity (segment_space seg)" by auto qed *)

(* typedef ('b::len0) size_t = "UNIV :: nat set" ..
instantiation size_t :: (len0) len begin
definition len_of_size_t :: "'a size_t itself \<Rightarrow> nat" where [simp]: "len_of_size_t _ = 1 + adrspace_capacity LENGTH('a)"
  \<comment> \<open>it is plus 1 to enable the representation of `negative` offset of the address exorcising any ambiguity.
    In the complication implementation, it is interpreted as this that the size of a single segment can only be at most to half of the
    actual total capacity of the address space, 2^31 bytes in the 32 bits machine, so that the size_t in this case still equals
    to that in the actual physical machine. \<close>
instance by standard auto
end *)

lemma memptr_exisits[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>addr. P (memptr addr))" by (metis memptr.exhaust) 
lemma memptr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>addr. P (memptr addr))" by (metis memptr.exhaust) 

subsection \<open>Instantiations for memptr\<close>

instantiation memptr :: (len0) lrep begin
definition llty_memptr :: " 'a memptr itself \<Rightarrow> llty" where "llty_memptr _ = llty_pointer LENGTH('a)"
definition deepize_memptr :: " 'a memptr \<Rightarrow> deep_model"
  where "deepize_memptr ptr = DM_pointer LENGTH('a) (case_memptr id ptr)"
definition shallowize_memptr :: " deep_model \<Rightarrow> 'a memptr "
  where "shallowize_memptr dm = (case dm of DM_pointer _ addr \<Rightarrow> memptr addr)"
instance apply standard using shallowize_memptr_def deepize_memptr_def by (auto split: memptr.split)
end

instantiation memptr :: (len0) field begin instance by standard end
instantiation memptr :: (len0) field_list begin instance by standard end

instantiation memptr :: (len0) zero begin
definition zero_memptr :: "'a memptr" where [simp]: "zero_memptr = memptr 0"
instance by standard
end

abbreviation "addr_allocated heap addr \<equiv> MemAddress addr \<in> dom heap"

instantiation memaddr :: ceq begin
definition ceqable_memaddr :: " heap \<Rightarrow> memaddr \<Rightarrow> memaddr \<Rightarrow> bool"
  where [simp]: "ceqable_memaddr heap x y = (addr_allocated heap x \<and> addr_allocated heap y)"
definition ceq_memaddr :: " memaddr \<Rightarrow> memaddr \<Rightarrow> bool" where [simp]: "ceq_memaddr = (=)"
instance by standard auto
end

instantiation memptr :: (len0) ceq begin
definition ceqable_memptr :: " heap \<Rightarrow> 'a memptr \<Rightarrow> 'a memptr \<Rightarrow> bool" where
  "ceqable_memptr heap x y = (case x of memptr a \<Rightarrow> case y of memptr b \<Rightarrow>
    addr_allocated heap a \<and> addr_allocated heap b)"
lemma [simp]: "ceqable heap (memptr a) (memptr b) = ceqable heap a b" unfolding ceqable_memptr_def by simp
definition ceq_memptr :: " 'a memptr \<Rightarrow> 'a memptr \<Rightarrow> bool" where [simp]: "ceq_memptr = (=)"
instance proof
  fix x y z :: " 'a memptr" and h :: heap
  show "ceqable h x y = ceqable h y x" by (cases x; cases y) simp
  show "ceqable h x x \<Longrightarrow> ceq x x" and "ceqable h x y \<Longrightarrow> ceq x y = ceq y x"
    and "ceqable h x y \<Longrightarrow> ceqable h y z \<Longrightarrow> ceqable h x z \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z" by auto+
qed
end

subsection \<open>\<nu>-abstraction\<close>

subsubsection \<open>None typed Pointer\<close>

definition Pointer' :: "('spc::len0) itself \<Rightarrow> ('spc memptr, memaddr) \<nu>"
  where "Pointer' _ h p x = (case p of (memptr i) \<Rightarrow> (i = x))"
syntax "_Pointer'_" :: "type \<Rightarrow> logic" (\<open>Pointer'[_']\<close>)
translations "Pointer['x]" == "CONST Pointer' (TYPE('x))" 
abbreviation "Pointer \<equiv> Pointer[0]"

lemma [simp]: "[heap] memptr i \<nuLinkL> Pointer' spc \<nuLinkR> i' \<longleftrightarrow> (i = i')" unfolding Pointer'_def Refining_ex by auto
lemma [elim,\<nu>elim]: " addr \<ratio> (Pointer' spc) \<Longrightarrow> C \<Longrightarrow> C" unfolding Inhabited_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Zero (Pointer' spc) 0" unfolding \<nu>Zero_def by simp
lemma [\<nu>intro]: "\<nu>Resources (Pointer' spc) (\<lambda>x. {})" unfolding \<nu>def by (simp add: lrep_exps)

subsubsection \<open>Typed Pointer\<close>

definition TypedPtr' :: "('spc::len0) itself \<Rightarrow> llty \<Rightarrow> ('spc memptr, memaddr) \<nu>"
  where "TypedPtr' _ ty h p x = (case p of (memptr i) \<Rightarrow> (i = x) \<and> memaddr_llty i = ty)"
syntax "_TypedPtr'_" :: "type \<Rightarrow> logic" (\<open>TypedPtr'[_']\<close>)
translations "TypedPtr['x]" == "CONST TypedPtr' (TYPE('x))" 
abbreviation "TypedPtr \<equiv> TypedPtr[0]"

lemma [simp]: "[heap] memptr i \<nuLinkL> TypedPtr' spc ty \<nuLinkR> i' \<longleftrightarrow> (i = i') \<and> memaddr_llty i = ty"
  unfolding TypedPtr'_def Refining_ex by auto
lemma [elim,\<nu>elim]: " addr \<ratio> TypedPtr' spc ty \<Longrightarrow> (memaddr_llty addr = ty \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def by (simp add: lrep_exps)
(* lemma [\<nu>intro]: "\<nu>Equal (TypedPtr' spc ty) ceqable (=)" unfolding \<nu>Equal_def by (simp add: lrep_exps) *)
lemma [\<nu>intro]: "\<nu>Resources (TypedPtr' spc ty) (\<lambda>x. {})" unfolding \<nu>def by (simp add: lrep_exps)

subsubsection \<open>Casts\<close>

named_theorems fixtyp_\<nu>cast and freetyp_\<nu>cast

lemma [\<nu>intro, fixtyp_\<nu>cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e memaddr_llty addr = ty \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t addr \<tycolon> Pointer['spc] \<longmapsto> addr \<tycolon> TypedPtr['spc::len0] ty"
  unfolding Cast_def by (cases addr) (auto simp add: lrep_exps split: memaddr.split)

lemma [\<nu>intro, freetyp_\<nu>cast]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t addr \<tycolon> TypedPtr['spc] ty \<longmapsto> addr \<tycolon> Pointer['spc::len0] \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e memaddr_llty addr = ty"
  unfolding Cast_def by (cases addr) (auto simp add: lrep_exps split: memaddr.split)

section \<open>Void\<close>

datatype void = void
declare void.split[split]

lemma [simp]: "x = y" for x :: void by (cases x; cases y) fast

subsection \<open>Settings\<close>

instantiation void :: stack begin
definition llty_void :: "void itself \<Rightarrow> llty" where "llty_void _ = llty_nil"
definition deepize_void :: "void \<Rightarrow> deep_model" where "deepize_void _ = DM_none"
instance by standard auto 
end


instantiation void :: field begin instance by standard end
instantiation void :: field_list begin instance by standard end

instantiation void :: zero begin
definition zero_void :: "void" where [simp]: "zero_void = void"
instance by standard
end


subsection \<open>Abstractor\<close>

definition Void :: "heap \<Rightarrow> void set" where "Void _ = {void}" 
text \<open>The name `void` coincides that, when a procedure has no input arguments,
  the \<nu>-type for the input would exactly be @{term Void}. \<close>
lemma [simp,intro]: "void \<in> Void res" unfolding Void_def by simp
lemma [simp,intro]: "Inhabited Void" unfolding Inhabited_def by auto
lemma [elim!, \<nu>elim]: "Inhabited Void \<Longrightarrow> C \<Longrightarrow> C" .
lemma [intro]: "NuSet Void" unfolding NuSet_def Void_def by simp
lemma [intro]: "\<nu>Resources_of_set Void {}" unfolding \<nu>Resources_of_set_def Void_def by fast
(*translations "a" <= "a \<^bold>a\<^bold>n\<^bold>d CONST Void"*)

section \<open>The integer data type\<close>

subsection \<open>Lrep instantiations\<close>

instantiation word :: (len) lrep begin
definition llty_word :: "'a word itself \<Rightarrow> llty" where [simp]: "llty_word _ = llty_int LENGTH('a)"
definition deepize_word :: " 'a word \<Rightarrow> deep_model " where "deepize_word x = DM_int LENGTH('a) (unat x)"
definition shallowize_word :: " deep_model \<Rightarrow> 'a word" where "shallowize_word x = (case x of DM_int _ n \<Rightarrow> of_nat n)"
instance apply standard using deepize_word_def shallowize_word_def by auto
end

instantiation word :: (len) ceq
begin
definition ceqable_word :: "heap \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> bool" where [simp]: "ceqable_word _ x y = True"
definition ceq_word :: "'a word \<Rightarrow>  'a word \<Rightarrow> bool" where [simp]: "ceq_word x y = (x = y)"
instance by standard (auto+)
end

instantiation word :: (len) field begin instance by standard end
instantiation word :: (len) field_list begin instance by standard end

subsection \<open>Basic \<nu>-abstractions based on integer type\<close>

subsubsection \<open>Natural number\<close>

definition NuNat :: "('a::len) itself \<Rightarrow> ('a word, nat) \<nu>" where "NuNat _ h p x = (unat p = x)"
syntax "_NuNat_" :: "type \<Rightarrow> logic" (\<open>\<nat>'[_']\<close>)
translations "\<nat>['x]" == "CONST NuNat (TYPE('x))" 

lemma [simp]: "[heap] p \<nuLinkL> NuNat b \<nuLinkR> x \<equiv> (unat p = x)" unfolding NuNat_def Refining_ex by auto
lemma [elim,\<nu>elim]: "x \<ratio> \<nat>['b::len] \<Longrightarrow> (x < 2^LENGTH('b) \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

lemma [\<nu>intro]: "\<nu>Equal (NuNat b) (\<lambda>x y. True) (=)"
  unfolding \<nu>Equal_def by (auto simp add: unsigned_word_eqI)
lemma [\<nu>intro]: "\<nu>Zero (NuNat b) 0" unfolding \<nu>Zero_def by simp
lemma [\<nu>intro]: "\<nu>Resources (NuNat b) (\<lambda>x. {})" unfolding \<nu>def by simp

definition NuNatRound :: "('a::len) itself \<Rightarrow> ('a word, nat) \<nu>" where "NuNatRound _ h p x = (p = of_nat x)"
syntax "_NuNatRound_" :: "type \<Rightarrow> logic" (\<open>\<nat>\<^sup>r'[_']\<close>)
translations "\<nat>\<^sup>r['x]" == "CONST NuNatRound (TYPE('x))" 

lemma [simp]: "[heap] p \<nuLinkL> NuNatRound b \<nuLinkR> x \<equiv> (p = of_nat x)" unfolding NuNatRound_def Refining_ex by auto
lemma [\<nu>intro]: "\<nu>Zero (NuNatRound b) 0" unfolding \<nu>Zero_def by simp

subsubsection \<open>Integer\<close>

definition NuInt :: "('a::len) itself \<Rightarrow> ('a word, int) \<nu>" where "NuInt _ h p x = (sint p = x)"
syntax "_NuInt_" :: "type \<Rightarrow> logic" (\<open>\<int>'[_']\<close>)
translations "\<int>['x]" == "CONST NuInt (TYPE('x))" 

lemma [simp]: "[heap] p \<nuLinkL> NuInt b \<nuLinkR> x \<equiv> (sint p = x)" unfolding NuInt_def Refining_ex by auto
lemma [elim,\<nu>elim]: "x \<ratio> \<int>['b::len] \<Longrightarrow> (x < 2^(LENGTH('b) - 1) \<Longrightarrow> -(2^(LENGTH('b)-1)) \<le> x \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def apply simp by (metis One_nat_def sint_ge sint_lt) 

lemma [\<nu>intro]: "\<nu>Equal (NuInt b) (\<lambda>x y. True) (=)" unfolding \<nu>Equal_def by (auto simp add: signed_word_eqI) 
lemma [\<nu>intro]: "\<nu>Zero (NuInt b) 0" unfolding \<nu>Zero_def by simp

subsubsection \<open>Boolean\<close>

lemma [simp]: "(x \<noteq> 1) = (x = 0)" for x :: "1 word" proof -
  have "(UNIV:: 1 word set) = {0,1}" unfolding UNIV_word_eq_word_of_nat
  using less_2_cases apply auto apply force
  by (metis UNIV_I UNIV_word_eq_word_of_nat len_num1 power_one_right)
  then show ?thesis  by auto
qed

definition NuBool :: "(1 word, bool) \<nu>" ("\<bool>") where "NuBool h p x = ((p = 1) = x)"
lemma [simp]: "[heap] p \<nuLinkL> \<bool> \<nuLinkR> x \<longleftrightarrow> (p = 1) = x" unfolding NuBool_def Refining_ex by simp
lemma [\<nu>intro]: "\<nu>Equal \<bool> (\<lambda>x y. True)  (=)" unfolding \<nu>Equal_def by auto

lemma [\<nu>intro]: "\<nu>Zero NuBool False" unfolding \<nu>Zero_def by simp

section \<open>Prod & the pair abstract structure\<close>

subsection \<open>Lrep instantiations\<close>

instantiation prod :: (field, field_list) field_list begin instance by standard end

instantiation prod :: (zero, zero) zero begin
definition zero_prod :: "'a \<times> 'b" where [simp]: "zero_prod = (0,0)"
instance by standard
end
instantiation prod :: (ceq, ceq) ceq begin
definition ceqable_prod :: "heap \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "ceqable_prod heap = ceqable heap \<times>\<^sub>r ceqable heap"
lemma [simp]: "ceqable heap (a1,b1) (a2,b2) \<longleftrightarrow> ceqable heap a1 a2 \<and> ceqable heap b1 b2" unfolding ceqable_prod_def by auto
definition ceq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "ceq_prod = ceq \<times>\<^sub>r ceq"
lemma [simp]: "ceq (a1,b1) (a2,b2) \<longleftrightarrow> ceq a1 a2 \<and> ceq b1 b2" unfolding ceq_prod_def by auto
instance by standard (auto intro: ceq_trans)
end

subsection \<open>Fusion \<nu>-abstraction\<close>

definition Fusion :: "('a1::lrep,'b1) \<nu> \<Rightarrow> ('a2::lrep,'b2) \<nu> \<Rightarrow> ('a1 \<times> 'a2, 'b1 \<times> 'b2) \<nu>" (infixr "\<nuFusion>" 70) 
  where "Fusion N M heap p x = (case p of (p1,p2) \<Rightarrow> case x of (x1,x2) \<Rightarrow> 
    ([heap] p1 \<nuLinkL> N \<nuLinkR> x1) \<and> ([heap] p2 \<nuLinkL> M \<nuLinkR> x2))"

lemma [simp]: "[heap] (p1,p2) \<nuLinkL> N \<nuFusion> M \<nuLinkR> (x1,x2) \<longleftrightarrow> ([heap] p1 \<nuLinkL> N \<nuLinkR> x1) \<and> ([heap] p2 \<nuLinkL> M \<nuLinkR> x2)" unfolding Fusion_def Refining_ex by simp
lemma [elim,\<nu>elim]: "(x1,x2) \<ratio> N1 \<nuFusion> N2 \<Longrightarrow> (x1 \<ratio> N1 \<Longrightarrow> x2 \<ratio> N2 \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

lemma [\<nu>intro]: "\<nu>Zero N z1 \<Longrightarrow> \<nu>Zero M z2 \<Longrightarrow> \<nu>Zero (N \<nuFusion> M) (z1,z2)" unfolding \<nu>Zero_def by simp

lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<longmapsto> x' \<tycolon> N' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t y \<tycolon> M \<longmapsto> y' \<tycolon> M' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e Q \<Longrightarrow>
  \<^bold>c\<^bold>a\<^bold>s\<^bold>t (x,y) \<tycolon> N \<nuFusion> M \<longmapsto> (x',y') \<tycolon> N' \<nuFusion> M' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<and> Q" unfolding Cast_def by auto

definition AutoFusion (infixr "\<nuFusion>''" 70)  where "AutoFusion = Fusion"
lemma [\<nu>intro]: "\<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuFusion> M \<longmapsto> x' \<tycolon> N' \<nuFusion> M' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P \<Longrightarrow> \<^bold>c\<^bold>a\<^bold>s\<^bold>t x \<tycolon> N \<nuFusion> M \<longmapsto> x' \<tycolon> N' \<nuFusion>' M' \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e P"
  unfolding Cast_def AutoFusion_def .

section \<open>Tuple\<close>

datatype 'a tuple = Tuple "('a::field_list)"

lemma tuple_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>x. P (Tuple x))" by (metis tuple.exhaust) 
lemma tuple_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>x. P (Tuple x))" by (metis tuple.exhaust) 

subsection \<open>Lrep instantiations\<close>

subsubsection \<open>lrep\<close>

instantiation tuple :: (field_list) lrep begin
definition llty_tuple :: " 'a tuple itself \<Rightarrow> llty " where [simp]: "llty_tuple _ = llty_tup (llty TYPE('a))"
definition deepize_tuple :: " 'a tuple \<Rightarrow> deep_model " where "deepize_tuple x = DM_record (deepize (case_tuple id x))"
definition shallowize_tuple :: " deep_model \<Rightarrow> 'a tuple " where "shallowize_tuple x = (case x of DM_record y \<Rightarrow> Tuple (shallowize y))"
instance apply standard using shallowize_tuple_def deepize_tuple_def by (auto split: tuple.split)
end

subsubsection \<open>zero\<close>

instantiation tuple :: ("{zero,field_list}") zero begin
definition zero_tuple :: " 'a tuple " where [simp]: "zero_tuple = Tuple 0"
instance by standard
end

subsubsection \<open>ceq\<close>

instantiation tuple :: ("{ceq,field_list}") ceq begin
definition ceqable_tuple :: " heap \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> bool " where "ceqable_tuple heap = rel_tuple (ceqable heap)"
definition ceq_tuple :: " 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> bool " where "ceq_tuple = rel_tuple ceq"
lemma [simp]: "ceqable heap (Tuple a) (Tuple b) = ceqable heap a b" unfolding ceqable_tuple_def by simp
lemma [simp]: "ceq (Tuple a) (Tuple b) = ceq a b" unfolding ceq_tuple_def by simp
instance proof
  fix x y z :: " 'a tuple" and h :: heap
  show "ceqable h x y = ceqable h y x" by (cases x; cases y) simp
  show "ceqable h x x \<Longrightarrow> ceq x x" by (cases x) auto
  show "ceqable h x y \<Longrightarrow> ceq x y = ceq y x" by (cases x; cases y) simp
  show "ceqable h x y \<Longrightarrow> ceqable h y z \<Longrightarrow> ceqable h x z \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z" by (cases x, cases y, cases z) (simp, blast intro: ceq_trans)
qed
end

subsubsection \<open>miscellaneous\<close>

instantiation tuple :: (field_list) field begin instance by standard end
instantiation tuple :: (field_list) field_list begin instance by standard end

subsection \<open>Nu abstraction - `NuTuple`\<close>

definition NuTuple :: "(('a::field_list), 'b) \<nu> \<Rightarrow> ('a tuple, 'b) \<nu>" ("\<lbrace> _ \<rbrace>") where "\<lbrace> N \<rbrace> h p x = (case p of Tuple p' \<Rightarrow> [h] p' \<nuLinkL> N \<nuLinkR> x)"

lemma [simp]: "[heap] Tuple p \<nuLinkL> \<lbrace> N \<rbrace> \<nuLinkR> x \<longleftrightarrow> [heap] p \<nuLinkL> N \<nuLinkR> x" unfolding NuTuple_def Refining_ex by simp
lemma [elim,\<nu>elim]: "x \<ratio> \<lbrace> N \<rbrace> \<Longrightarrow> (x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def tuple_exists by simp

lemma [\<nu>intro]: "\<nu>Equal N P eq \<Longrightarrow> \<nu>Equal \<lbrace> N \<rbrace> P eq" unfolding \<nu>Equal_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>Zero N z \<Longrightarrow> \<nu>Zero \<lbrace> N \<rbrace> z" unfolding \<nu>Zero_def by simp
lemma [\<nu>intro]: "NuSet \<tort_lbrace> x \<tycolon> T \<tort_rbrace> \<Longrightarrow> NuSet \<tort_lbrace> x \<tycolon> \<lbrace> T \<rbrace> \<tort_rbrace>" unfolding NuSet_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Resources T rcss \<Longrightarrow> \<nu>Resources \<lbrace> T \<rbrace> rcss" unfolding \<nu>def by (simp add: lrep_exps)

end