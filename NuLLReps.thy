theory NuLLReps
  imports NuPrim  "HOL-Library.Word"
  abbrevs "<own>" = "\<left_fish_tail>"
    and "<none>" = "\<down_fish_tail>"
    and "<object>" = "\<R_arr_tail>"
    and "<pointer>"  = "\<TeardropAsterisk>"
begin   

text \<open>Semantic data representations\<close>

named_theorems lrep_exps
declare pair_forall[lrep_exps] pair_exists[lrep_exps]

section \<open>Preliminary notions\<close>

class field = lrep
class field_list = lrep

section \<open>The construction state\<close>

instantiation state :: (lrep) lrep begin
definition llty_state :: "'a state itself \<Rightarrow> llty" where [simp]: "llty_state _ = la_z"
instance by standard
end

section \<open>Owning\<close>

datatype 'a owning = Owning zint 'a (infixr "\<left_fish_tail>" 60) | OwnNone ("\<down_fish_tail>")
  \<comment> \<open>\<^term>\<open>quantity_of_ownership \<left_fish_tail> data\<close>\<close>
  
lemma owning_forall[lrep_exps]: "All P \<longleftrightarrow> P \<down_fish_tail> \<and> (\<forall>z x. P (z \<left_fish_tail> x))" by (metis owning.exhaust) 
lemma owning_exists[lrep_exps]: "Ex P \<longleftrightarrow> P \<down_fish_tail> \<or> (\<exists>z x. P (z \<left_fish_tail> x))" by (metis owning.exhaust) 

definition "rel1_owning R x y = (case x of zx \<left_fish_tail> ax \<Rightarrow> (case y of zy \<left_fish_tail> ay \<Rightarrow> R ax ay | _ \<Rightarrow> False)  | _ \<Rightarrow> False)"
lemma [simp]: "rel1_owning R (zx \<left_fish_tail> ax) (zy \<left_fish_tail> ay) = R ax ay"
  and [simp]: "rel1_owning R \<down_fish_tail> y = False" and [simp]: "rel1_owning R x \<down_fish_tail> = False"
  unfolding rel1_owning_def by (auto split: owning.split)

subsection \<open>Instantiations\<close>

instantiation owning :: (disposable) disposable begin
definition disposable_owning :: " 'a owning \<Rightarrow> bool"
  where "disposable_owning x = (case x of Owning z a \<Rightarrow> disposable a | _ \<Rightarrow> True)"
lemma [simp]: "disposable (Owning z a) = disposable a" and [simp]: "disposable OwnNone = True"
  unfolding disposable_owning_def by simp+
instance by standard
end

instantiation owning :: (disposable) lrep begin
definition llty_owning :: " 'a owning itself \<Rightarrow> llty" where "llty_owning _ = la_z"
instance by standard
end

instantiation owning :: (disposable) field begin instance by standard end
instantiation owning :: (disposable) field_list begin instance by standard end

instantiation owning :: (sharing_identical) sharing_identical begin
definition sharing_identical_owning :: " 'a owning \<Rightarrow> 'a owning \<Rightarrow> bool "
  where "sharing_identical_owning = rel_owning sharing_identical"
lemma [simp]: "sharing_identical (Owning z1 x1) (Owning z2 x2) \<longleftrightarrow> (z1 = z2) \<and> sharing_identical x1 x2"
  and [simp]: "sharing_identical (Owning z1 x1) OwnNone \<longleftrightarrow> False"
  and [simp]: "sharing_identical OwnNone (Owning z2 x2) \<longleftrightarrow> False"
  and [simp]: "sharing_identical OwnNone OwnNone \<longleftrightarrow> True"
  unfolding sharing_identical_owning_def by simp+
instance proof
  fix x y z :: \<open>'a owning\<close> and a b :: zint
  show "sharing_identical x x" by (cases x) simp+
  show "sharing_identical x y = sharing_identical y x" by (cases x; cases y) auto
  show "sharing_identical x y \<Longrightarrow> sharing_identical y z \<Longrightarrow> sharing_identical x z" by (cases x; cases y; cases z) (auto intro: sharing_identical_trans)
qed
end

instantiation owning :: (type) ownership begin
definition ownership_owning :: " 'a owning \<Rightarrow> ownership"
  where "ownership_owning x = (case x of Owning z _ \<Rightarrow> OWS_1 z | OwnNone \<Rightarrow> OWS_0)"
lemma [simp]: "ownership (Owning z x) = OWS_1 z" and [simp]: "ownership OwnNone = OWS_0"
  unfolding ownership_owning_def by simp+
instance by standard
end

instantiation owning :: (type) share begin
definition shareable_owning :: " 'a owning \<Rightarrow> bool " where [simp]: "shareable_owning _ = True"
definition share_owning :: " zint \<Rightarrow> 'a owning \<Rightarrow> 'a owning "
  where "share_owning z x = (case x of Owning z' a \<Rightarrow> Owning (z' + z) a | _ \<Rightarrow> OwnNone)"
definition dpriv_owning :: " 'a owning \<Rightarrow> 'a owning" where [simp]: "dpriv_owning x = OwnNone"

lemma [simp]: "share z (Owning z' a) = Owning (z' + z) a" and [simp]: "share z OwnNone = OwnNone"
  unfolding share_owning_def by simp+

instance proof
  fix x y z :: \<open>'a owning\<close> and a b :: zint
  show "share (Gi 0) x = x" by (cases x) auto
  show "share b (share a x) = share (a + b) x" by (cases x) (auto simp add: add.assoc)
qed
end

instantiation owning :: (type) ceq begin
definition ceqable_owning :: " 'a owning \<Rightarrow> 'a owning \<Rightarrow> bool" where [simp]: "ceqable_owning _ _ = True"
definition ceq_owning :: " 'a owning \<Rightarrow> 'a owning \<Rightarrow> bool" where [simp]: "ceq_owning _ _ = True"
instance by standard auto
end

instantiation owning :: (type) zero begin
definition zero_owning :: " 'a owning" where [simp]: "zero_owning = \<down_fish_tail>"
instance by standard
end

section \<open>Identifier\<close>

datatype identifier = idhypen identifier nat (infixl "\<hyphen>" 64) | ID_MEM | ID_CONST string
  \<comment> \<open>A tree-like structure allowing infinite sub identifier space, like folders where infinite sub-folders can be allocated\<close>

definition alloc_identifier :: "identifier \<Rightarrow> identifier"
  where "alloc_identifier x = (case x of i\<hyphen>j \<Rightarrow> i\<hyphen>(j + 1))"
definition alloc_identifier_space :: "identifier \<Rightarrow> identifier"
  where [simp]: "alloc_identifier_space x = x\<hyphen>0"

lemma [simp]: "alloc_identifier (i\<hyphen>j) = (i\<hyphen>(j + 1))" unfolding alloc_identifier_def by simp

text \<open>Identifier itself is the low representation of identifier source, an abstract value used for assigning identifiers.\<close>

subsection \<open>Instantiations\<close>

instantiation identifier :: lrep begin
definition llty_identifier :: " identifier itself \<Rightarrow> llty" where [simp]: "llty_identifier _ = la_z"
definition disposable_identifier :: " identifier \<Rightarrow> bool" where [simp]: "disposable_identifier _ = True"
instance by standard
end

instantiation identifier :: field begin instance by standard end
instantiation identifier :: field_list begin instance by standard end

instantiation identifier :: ceq begin
definition ceqable_identifier :: "identifier \<Rightarrow> identifier \<Rightarrow> bool" where [simp]: "ceqable_identifier _ _ = True"
definition ceq_identifier :: "identifier \<Rightarrow> identifier \<Rightarrow> bool" where [simp]: "ceq_identifier _ _ = True"
instance by standard auto
end

instantiation identifier :: ownership begin
definition ownership_identifier :: "identifier \<Rightarrow> ownership" where [simp]: "ownership_identifier _ = OWS_0"
instance by standard
end

lemma [\<nu>intro]: "\<nu>Ownership N (\<lambda>x. OWS_0)" for N :: "(identifier, identifier) nu" unfolding \<nu>Ownership_def by simp
lemma [\<nu>intro]: "\<nu>Disposable S" for S :: "identifier set" unfolding \<nu>Disposable_def by simp

subsection \<open>\<nu>-abstraction for Identifier Source\<close>

definition IdSrc :: "(identifier, identifier) nu" where "IdSrc p x = (p = x)"
lemma [simp]: "p \<nuLinkL> IdSrc \<nuLinkR> x \<longleftrightarrow> (p = x)" unfolding Refining_ex IdSrc_def by simp

lemma [\<nu>intro]: "\<nu>CEqual IdSrc (\<lambda>x y. True) (\<lambda>x y. True)" unfolding \<nu>CEqual_def by simp

section \<open>Memory address\<close>

datatype memadr = memadr (segment_of_adr: identifier) (offset_of_adr: int) (infix "|+" 60) \<comment> \<open>identifier to the segment, offset in the segment\<close>
datatype ('spc::len0) memptr = memptr "memadr owning"  \<comment> \<open>'spc : address space\<close>

consts size_of :: "llty \<Rightarrow> nat" \<comment> \<open>in unit of bytes\<close>
consts segment_len :: "identifier \<Rightarrow> nat" \<comment> \<open>in unit of the number of elements\<close>
consts segment_llty :: "identifier \<Rightarrow> llty" \<comment> \<open>type of the element in the segment\<close>
consts segment_space :: "identifier \<Rightarrow> nat" \<comment> \<open>LLVM address space of the segment\<close>
consts adrspace_capacity :: "nat \<Rightarrow> nat" \<comment> \<open>in unit of bits\<close>
specification (adrspace_capacity) adrspace_capacity_L0[intro]: "0 < adrspace_capacity spc" by auto
specification (segment_len) segment_len_max: "segment_len seg < (2::nat) ^ adrspace_capacity (segment_space seg)"
  proof show "\<forall>seg. (\<lambda>x. 0) seg < (2::nat) ^ adrspace_capacity (segment_space seg)" by auto qed
(* specification (segment_len) segment_len_max: "segment_len seg * size_of (segment_llty seg) < adrspace_capacity (segment_space seg)"
  proof show "\<forall>seg. (\<lambda>x. 0) seg * size_of (segment_llty seg) < adrspace_capacity (segment_space seg)" by auto qed *)

typedef ('b::len0) size_t = "UNIV :: nat set" ..
instantiation size_t :: (len0) len begin
definition len_of_size_t :: "'a size_t itself \<Rightarrow> nat" where [simp]: "len_of_size_t _ = 1 + adrspace_capacity LENGTH('a)"
  \<comment> \<open>it is plus 1 to enable the representation of `negative` offset of the address exorcising any ambiguity.
    In the complication implementation, it is interpreted as this that the size of a single segment can only be at most to half of the
    actual total capacity of the address space, 2^31 bytes in the 32 bits machine, so that the size_t in this case still equals
    to that in the actual physical machine. \<close>
instance by standard auto
end

abbreviation "memadr_len a \<equiv> segment_len (segment_of_adr a)"
abbreviation "memadr_llty a \<equiv> segment_llty (segment_of_adr a)"

abbreviation within_seg :: "nat \<Rightarrow> memadr \<Rightarrow> bool" where "within_seg len a \<equiv> 0 \<le> offset_of_adr a \<and> nat (offset_of_adr a) + len \<le> memadr_len a"

text \<open>A memory address is represented by an identifier, which is a number sequence, in the specific form
  \<^term>\<open>id_to_segment\<hyphen>index_of_the_addressing_element_in_this_segment\<close>.
  
  The ownership here ensures when releasing the segment to which the address points, which requires the total ownership,
  all holdings of this address are eliminated, so that no any copy will attend further computation.
  It is significant when the released segment is recycled and allocated in the future, conflicting with obsolete dangling pointers.

  The address \<^term>\<open>Seg\<hyphen>i\<close> is within the allocated segment only if i < segment_len (Seg\<hyphen>i).
  Only within addresses can be compared between different segments. In the same segment, only within addresses and that at
  the end edge can be compared (equality and quantitative).

  Pointer to field of a record structure is not supported, whereas shifting of pointers to elements of an array is supported.
  Considering field-pointing is an obsolete feature in modern languages, it is worthy to be sacrificed for the sake of the 
  simplicity of the model, especially when this feature can be replaced by splitting the record into multiple small allocation units
  at the cost of memory consumption. I admit it leads to memory fragment. This research totally is an adventure.
  
  This also means the fix-sized array embedded in the record structure also has to be allocated separately,
  in a fashion with no distinction with indeterminate-sized array. I admit this hinders both time and memory performance.
\<close>

lemma memptr_exisits[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>id. P (memptr id))" by (metis memptr.exhaust) 
lemma memptr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>id. P (memptr id))" by (metis memptr.exhaust) 
lemma memadr_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>s i. P (s |+ i))" by (metis memadr.exhaust)
lemma memadr_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>s i. P (s |+ i))" by (metis memadr.exhaust)

subsection \<open>Instantiations for memptr\<close>

instantiation memptr :: (len0) lrep begin
definition disposable_memptr :: "'a memptr \<Rightarrow> bool" where [simp]: "disposable_memptr _ = True"
definition llty_memptr :: "'a memptr itself \<Rightarrow> llty" where [simp]: "llty_memptr _ = la_p LENGTH('a)"
instance by standard
end

instantiation memptr :: (len0) field begin instance by standard end
instantiation memptr :: (len0) field_list begin instance by standard end

instantiation memptr :: (len0) sharing_identical begin
definition sharing_identical_memptr :: " 'a memptr \<Rightarrow> 'a memptr \<Rightarrow> bool" where [simp]: "sharing_identical_memptr = (=)"
instance by standard auto
end

instantiation memptr :: (len0) share begin
definition shareable_memptr :: " 'a memptr \<Rightarrow> bool" where [simp]: "shareable_memptr _ = True"
definition share_memptr :: "zint \<Rightarrow> 'a memptr \<Rightarrow> 'a memptr"
  where "share_memptr z x = (case x of memptr a \<Rightarrow> memptr (share z a))"
definition dpriv_memptr :: "'a memptr \<Rightarrow> 'a memptr"
  where "dpriv_memptr x = (case x of memptr a \<Rightarrow> memptr (dpriv a))"
lemma [simp]: "share z (memptr x) = memptr (share z x)" unfolding share_memptr_def by simp
lemma [simp]: "dpriv (memptr x) = memptr (dpriv x)" unfolding dpriv_memptr_def by simp
instance proof
  fix x :: "'a memptr" and a b :: zint
  show "share (Gi 0) x = x" by (cases x) simp
  show "share b (share a x) = share (a + b) x" by (cases x) simp
qed
end

instantiation memptr :: (len0) ownership begin
definition ownership_memptr :: " 'a memptr \<Rightarrow> ownership" where [simp]: "ownership_memptr = case_memptr ownership"
instance by standard
end

text \<open>At end of every segment, one additional byte is appended to be allocated more, used for
  the placeholder of the end pointer, to prevent the potential conflict of addresses between this end
  and beginning of another segment. One byte is enough, because field-pointing (GetElementPtr) is not
  supported. Thanking to this, the ceq of the address model can be defined as:\<close>

inductive ceqable_adr where
  [intro,simp]: "(within_seg 0 a1 \<and> within_seg 0 a2) \<Longrightarrow> ceqable_adr a1 a2"
| [simp]: "ceqable_adr x y \<Longrightarrow> ceqable_adr y x"

instantiation memptr :: (len0) ceq begin
definition ceqable_memptr :: " 'a memptr \<Rightarrow> 'a memptr \<Rightarrow> bool" where
  "ceqable_memptr x y = (case x of memptr a \<Rightarrow> case y of memptr b \<Rightarrow> rel1_owning ceqable_adr a b)"
lemma [simp]: "ceqable (memptr a) (memptr b) = rel1_owning ceqable_adr a b" unfolding ceqable_memptr_def by simp
definition ceq_memptr :: " 'a memptr \<Rightarrow> 'a memptr \<Rightarrow> bool" where [simp]: "ceq_memptr = (=)"
instance proof
  fix x y z :: " 'a memptr"
  show "ceqable x y = ceqable y x" apply (cases x; cases y) apply simp subgoal for a b by (cases a; cases b) auto done
  show "ceqable x x \<Longrightarrow> ceq x x" and "ceqable x y \<Longrightarrow> ceq x y = ceq y x"
    and "ceqable x y \<Longrightarrow> ceqable y z \<Longrightarrow> ceqable x z \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z" by auto+
qed
end

instantiation memptr :: (len0) zero begin
definition zero_memptr :: " 'a memptr" where [simp]: "zero_memptr = memptr \<down_fish_tail>"
instance by standard
end

lemma [\<nu>intro]: "\<nu>Disposable S" for S :: "('spc0::len0) memptr set" unfolding \<nu>Disposable_def by simp

subsection \<open>\<nu>-abstraction\<close>

subsubsection \<open>Pointer\<close>

definition FreePtr' :: "('spc::len0) itself \<Rightarrow> ('spc memptr, memadr owning) nu"
  where "FreePtr' _ p x = (case p of (memptr i) \<Rightarrow> (i = x) \<and> pred_owning (within_seg 0) i)"
syntax "_FreePtr'_" :: "type \<Rightarrow> logic" (\<open>FreePtr'[_']\<close>)
translations "FreePtr['x]" == "CONST FreePtr' (TYPE('x))" 
abbreviation "FreePtr \<equiv> FreePtr[0]"

lemma [simp]: "memptr i \<nuLinkL> FreePtr['spc::len0] \<nuLinkR> i' \<longleftrightarrow> (i = i') \<and> pred_owning (within_seg 0) i'" unfolding FreePtr'_def Refining_ex by auto
lemma [elim,\<nu>elim]: "z \<left_fish_tail> i \<ratio> FreePtr['spc::len0] \<Longrightarrow> (within_seg 0 i \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (simp add: lrep_exps)

lemma [\<nu>intro]: "\<nu>CEqual FreePtr['spc::len0] (rel1_owning (\<lambda>x y. True)) (=)" unfolding \<nu>CEqual_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Share FreePtr['spc::len0] (\<lambda>x. True) share" unfolding \<nu>Share_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>ShrIdentical FreePtr['spc::len0] (=)" unfolding \<nu>ShrIdentical_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Deprive FreePtr['spc::len0] dpriv" unfolding \<nu>Deprive_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Ownership FreePtr['spc::len0] ownership" unfolding \<nu>Ownership_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Zero FreePtr['spc::len0] \<down_fish_tail>" unfolding \<nu>Zero_def by simp

subsubsection \<open>Slide pointer\<close>

definition SlidePtr' :: " ('spc::len0) itself \<Rightarrow> llty \<Rightarrow> ('spc memptr, memadr owning) nu"
  where "SlidePtr' _ ty p x = (case p of (memptr ap) \<Rightarrow> ap = x \<and> pred_owning (\<lambda>a. memadr_llty a = ty) x)"
syntax "_SlidePtr'_" :: "type \<Rightarrow> logic" (\<open>SlidePtr'[_']\<close>)
translations "SlidePtr['x]" == "CONST SlidePtr' (TYPE('x))" 
abbreviation "SlidePtr \<equiv> SlidePtr[0]"

lemma [simp]: "memptr i \<nuLinkL> SlidePtr['spc::len0] ty \<nuLinkR> i' \<longleftrightarrow> (i = i') \<and> pred_owning (\<lambda>a. memadr_llty a = ty) i'"
  unfolding SlidePtr'_def Refining_ex by auto
lemma [elim,\<nu>elim]: " z \<left_fish_tail> a \<ratio> SlidePtr['spc::len0] ty \<Longrightarrow> (memadr_llty a = ty \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (cases a) (simp add: lrep_exps)

lemma [\<nu>intro]: "\<nu>CEqual (SlidePtr['spc::len0] ty) (rel1_owning ceqable_adr) (=)" unfolding \<nu>CEqual_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Share (SlidePtr['spc::len0] ty) (\<lambda>x. True) share" unfolding \<nu>Share_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>ShrIdentical (SlidePtr['spc::len0] ty) (=)" unfolding \<nu>ShrIdentical_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Deprive (SlidePtr['spc::len0] ty) dpriv" unfolding \<nu>Deprive_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Ownership (SlidePtr['spc::len0] ty) ownership" unfolding \<nu>Ownership_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Zero (SlidePtr['spc::len0] ty) \<down_fish_tail>" unfolding \<nu>Zero_def by simp

subsubsection \<open>Typed Pointer\<close>

definition Pointer' :: "('spc::len0) itself \<Rightarrow> llty \<Rightarrow> ('spc memptr, memadr owning) nu"
  where "Pointer' _ ty p x = (case p of (memptr i) \<Rightarrow> (i = x) \<and> pred_owning (within_seg 0) x \<and> pred_owning (\<lambda>a. memadr_llty a = ty) x)"
syntax "_Pointer'_" :: "type \<Rightarrow> logic" (\<open>Pointer'[_']\<close>)
translations "Pointer['x]" == "CONST Pointer' (TYPE('x))" 
abbreviation "Pointer \<equiv> Pointer[0]"

lemma [simp]: "memptr i \<nuLinkL> Pointer['spc::len0] ty \<nuLinkR> i' \<longleftrightarrow>
    (i = i') \<and> pred_owning (within_seg 0) i \<and> pred_owning (\<lambda>a. memadr_llty a = ty) i'"
  unfolding Pointer'_def Refining_ex by auto
lemma [elim,\<nu>elim]: " z \<left_fish_tail> a \<ratio> Pointer['spc::len0] ty \<Longrightarrow> (memadr_llty a = ty \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by (cases a) (simp add: lrep_exps)

lemma [\<nu>intro]: "\<nu>CEqual (Pointer['spc::len0] ty) (rel1_owning ceqable_adr) (=)" unfolding \<nu>CEqual_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Share (Pointer['spc::len0] ty) (\<lambda>x. True) share" unfolding \<nu>Share_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>ShrIdentical (Pointer['spc::len0] ty) (=)" unfolding \<nu>ShrIdentical_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Deprive (Pointer['spc::len0] ty) dpriv" unfolding \<nu>Deprive_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Ownership (Pointer['spc::len0] ty) ownership" unfolding \<nu>Ownership_def by (simp add: lrep_exps)
lemma [\<nu>intro]: "\<nu>Zero (Pointer['spc::len0] ty) \<down_fish_tail>" unfolding \<nu>Zero_def by simp

subsubsection \<open>Casts\<close>

named_theorems slide_\<nu>cast and fixtyp_\<nu>cast and freetyp_\<nu>cast

lemma [\<nu>intro, slide_\<nu>cast]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> Pointer['spc] ty \<longmapsto> a \<tycolon> SlidePtr['spc::len0] ty \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e pred_owning (within_seg 0) a "
  unfolding Cast_def by (cases a) (auto split: memadr.split simp add: lrep_exps)

lemma [\<nu>intro, slide_\<nu>cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e pred_owning (\<lambda>x. memadr_llty x = ty) a \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> FreePtr['spc] \<longmapsto> a \<tycolon> SlidePtr['spc::len0] ty \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e pred_owning (within_seg 0) a "
  unfolding Cast_def by (cases a) (auto split: memadr.split simp add: lrep_exps)

lemma [\<nu>intro, fixtyp_\<nu>cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e pred_owning (within_seg 0) a \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> SlidePtr['spc] ty \<longmapsto> a \<tycolon> Pointer['spc::len0] ty"
  unfolding Cast_def by (cases a) (auto simp add: lrep_exps split: memadr.split)

lemma [\<nu>intro, fixtyp_\<nu>cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e pred_owning (\<lambda>x. memadr_llty x = ty) a \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> FreePtr['spc] \<longmapsto> a \<tycolon> Pointer['spc::len0] ty"
  unfolding Cast_def by (cases a) (auto simp add: lrep_exps split: memadr.split)

lemma [\<nu>intro, freetyp_\<nu>cast]:
  "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e pred_owning (within_seg 0) a \<Longrightarrow>
    \<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> SlidePtr['spc] ty \<longmapsto> a \<tycolon> FreePtr['spc::len0]  \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e pred_owning (\<lambda>x. memadr_llty x = ty) a"
  unfolding Cast_def by (cases a) (auto simp add: lrep_exps split: memadr.split)

lemma [\<nu>intro, freetyp_\<nu>cast]:
  "\<^bold>c\<^bold>a\<^bold>s\<^bold>t a \<tycolon> Pointer['spc] ty \<longmapsto> a \<tycolon> FreePtr['spc::len0] \<^bold>m\<^bold>e\<^bold>a\<^bold>n\<^bold>w\<^bold>h\<^bold>i\<^bold>l\<^bold>e pred_owning (\<lambda>x. memadr_llty x = ty) a"
  unfolding Cast_def by (cases a) (auto simp add: lrep_exps split: memadr.split)

section \<open>Void\<close>

instantiation void :: naive_lrep begin
definition share_void :: "zint \<Rightarrow> void \<Rightarrow> void" where [simp]: "share_void z = id"
definition shareable_void :: "void \<Rightarrow> bool" where [simp]: "shareable_void _ = True"
definition sharing_identical_void :: "void \<Rightarrow> void \<Rightarrow> bool" where [simp]: "sharing_identical_void x y = True"
definition dpriv_void :: "void \<Rightarrow> void" where [simp]: "dpriv_void x = x"
instance by standard auto
end

instantiation void :: field begin instance by standard end
instantiation void :: field_list begin instance by standard end

instantiation void :: ownership begin
definition ownership_void :: "void \<Rightarrow> ownership" where [simp]: "ownership_void _ = OWS_0"
instance by standard
end

instantiation void :: zero begin
definition zero_void :: "void" where [simp]: "zero_void = void"
instance by standard
end

lemma [\<nu>intro]: "\<nu>Ownership N (\<lambda>x. OWS_0)" for N :: "(void, 'b) nu" unfolding \<nu>Ownership_def by simp

section \<open>The integer data type\<close>

subsection \<open>Lrep instantiations\<close>

instantiation word :: (len) naive_lrep
begin
definition llty_word :: "'a word itself \<Rightarrow> llty" where [simp]: "llty_word _ = la_i LENGTH('a)"
definition share_word :: "zint \<Rightarrow> 'a word \<Rightarrow> 'a word" where [simp]: "share_word z = id"
definition shareable_word :: "'a word \<Rightarrow> bool" where [simp]: "shareable_word _ = True"
definition sharing_identical_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where [simp]: "sharing_identical_word x y = True"
definition dpriv_word :: "'a word \<Rightarrow> 'a word" where [simp]: "dpriv_word x = x"
definition disposable_word :: "'a word \<Rightarrow> bool" where [simp]: "disposable_word _ = True"
instance by standard auto
end

instantiation word :: (len) ownership begin
definition ownership_word :: " 'a word \<Rightarrow> ownership" where [simp]: "ownership_word _ = OWS_0"
instance by standard
end

lemma [\<nu>intro]: "\<nu>Ownership N (\<lambda>x. OWS_0)" for N :: "(('len::len) word, 'b) nu" unfolding \<nu>Ownership_def by simp

instantiation word :: (len) ceq
begin
definition ceqable_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where [simp]: "ceqable_word x y = True"
definition ceq_word :: "'a word \<Rightarrow>  'a word \<Rightarrow> bool" where [simp]: "ceq_word x y = (x = y)"
instance by standard (auto+)
end

instantiation word :: (len) field begin instance by standard end
instantiation word :: (len) field_list begin instance by standard end

subsection \<open>Basic \<nu>-abstractions based on integer type\<close>

subsubsection \<open>Natural number\<close>

definition NuNat :: "('a::len) itself \<Rightarrow> ('a word, nat) nu" where "NuNat _ p x = (unat p = x)"
syntax "_NuNat_" :: "type \<Rightarrow> logic" (\<open>\<nat>'[_']\<close>)
translations "\<nat>['x]" == "CONST NuNat (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuNat b \<nuLinkR> x \<equiv> (unat p = x)" unfolding NuNat_def Refining_ex by auto
lemma [elim,\<nu>elim]: "x \<ratio> \<nat>['b::len] \<Longrightarrow> (x < 2^LENGTH('b) \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by auto

lemma [\<nu>intro]: "\<nu>CEqual (NuNat b) (\<lambda>x y. True) (=)"
  unfolding \<nu>CEqual_def by (auto simp add: unsigned_word_eqI)
lemma [\<nu>intro]: "\<nu>Zero (NuNat b) 0" unfolding \<nu>Zero_def by simp

definition NuNatRound :: "('a::len) itself \<Rightarrow> ('a word, nat) nu" where "NuNatRound _ p x = (p = of_nat x)"
syntax "_NuNatRound_" :: "type \<Rightarrow> logic" (\<open>\<nat>\<^sup>r'[_']\<close>)
translations "\<nat>\<^sup>r['x]" == "CONST NuNatRound (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuNatRound b \<nuLinkR> x \<equiv> (p = of_nat x)" unfolding NuNatRound_def Refining_ex by auto
lemma [\<nu>intro]: "\<nu>Zero (NuNatRound b) 0" unfolding \<nu>Zero_def by simp

subsubsection \<open>Integer\<close>

definition NuInt :: "('a::len) itself \<Rightarrow> ('a word, int) nu" where "NuInt _ p x = (sint p = x)"
syntax "_NuInt_" :: "type \<Rightarrow> logic" (\<open>\<int>'[_']\<close>)
translations "\<int>['x]" == "CONST NuInt (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuInt b \<nuLinkR> x \<equiv> (sint p = x)" unfolding NuInt_def Refining_ex by auto
lemma [elim,\<nu>elim]: "x \<ratio> \<int>['b::len] \<Longrightarrow> (x < 2^(LENGTH('b) - 1) \<Longrightarrow> -(2^(LENGTH('b)-1)) \<le> x \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def apply simp by (metis One_nat_def sint_ge sint_lt) 

lemma [\<nu>intro]: "\<nu>CEqual (NuInt b) (\<lambda>x y. True) (=)" unfolding \<nu>CEqual_def by (auto simp add: signed_word_eqI) 
lemma [\<nu>intro]: "\<nu>Zero (NuInt b) 0" unfolding \<nu>Zero_def by simp

subsubsection \<open>Boolean\<close>

lemma [simp]: "(x \<noteq> 1) = (x = 0)" for x :: "1 word" proof -
  have "(UNIV:: 1 word set) = {0,1}" unfolding UNIV_word_eq_word_of_nat
  using less_2_cases apply auto apply force
  by (metis UNIV_I UNIV_word_eq_word_of_nat len_num1 power_one_right)
  then show ?thesis  by auto
qed

definition NuBool :: "(1 word, bool) nu" ("\<bool>") where "NuBool p x = ((p = 1) = x)"
lemma [simp]: "p \<nuLinkL> \<bool> \<nuLinkR> x \<longleftrightarrow> (p = 1) = x" unfolding NuBool_def Refining_ex by simp
lemma [\<nu>intro]: "\<nu>CEqual \<bool> (\<lambda>x y. True)  (=)" unfolding \<nu>CEqual_def by auto

lemma [\<nu>intro]: "\<nu>Zero NuBool False" unfolding \<nu>Zero_def by simp

section \<open>Prod & the pair abstract structure\<close>

subsection \<open>Lrep instantiations\<close>

instantiation prod :: (field, field_list) field_list begin instance by standard end

instantiation prod :: (zero, zero) zero begin
definition zero_prod :: "'a \<times> 'b" where [simp]: "zero_prod = (0,0)"
instance by standard
end

instantiation prod :: (ownership, ownership) ownership begin
definition ownership_prod :: " 'a \<times> 'b \<Rightarrow> ownership"
  where "ownership_prod x = (case x of (a,b) \<Rightarrow> OWS_C (ownership a) (ownership b))"
lemma [simp]: "ownership (a,b) = OWS_C (ownership a) (ownership b)" unfolding ownership_prod_def by simp
instance by standard
end

instantiation prod :: (sharing_identical, sharing_identical) sharing_identical begin
definition sharing_identical_prod :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" where "sharing_identical_prod = sharing_identical \<times>\<^sub>r sharing_identical"
lemma [simp]: "sharing_identical (a1,b1) (a2,b2) \<longleftrightarrow> sharing_identical a1 a2 \<and> sharing_identical b1 b2"
  unfolding sharing_identical_prod_def by simp
instance by standard (auto intro: sharing_identical_trans)
end

instantiation prod :: (share, share) share begin
definition shareable_prod :: "('a \<times> 'b) \<Rightarrow> bool" where "shareable_prod = shareable \<times>\<^sub>p shareable"
definition share_prod :: "zint \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where [simp]: "share_prod z x = (case x of (a,b) \<Rightarrow> (share z a, share z b))"
definition dpriv_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where [simp]: "dpriv_prod x = (case x of (a,b) \<Rightarrow> (dpriv a, dpriv b))"
lemma [simp]: "shareable (a,b) \<longleftrightarrow> shareable a \<and> shareable b" unfolding shareable_prod_def by simp
instance by standard auto
end

instantiation prod :: (naive_lrep, naive_lrep) naive_lrep
  begin instance by standard auto end

instantiation prod :: (ceq, ceq) ceq begin
definition ceqable_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "ceqable_prod  = ceqable \<times>\<^sub>r ceqable"
lemma [simp]: "ceqable (a1,b1) (a2,b2) \<longleftrightarrow> ceqable a1 a2 \<and> ceqable b1 b2" unfolding ceqable_prod_def by auto
definition ceq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "ceq_prod = ceq \<times>\<^sub>r ceq"
lemma [simp]: "ceq (a1,b1) (a2,b2) \<longleftrightarrow> ceq a1 a2 \<and> ceq b1 b2" unfolding ceq_prod_def by auto
instance by standard (auto intro: ceq_trans)
end

subsection \<open>Fusion \<nu>-abstraction\<close>

definition Fusion :: "('a1::lrep,'b1) nu \<Rightarrow> ('a2::lrep,'b2) nu \<Rightarrow> ('a1 \<times> 'a2, 'b1 \<times> 'b2) nu" (infixr "\<nuFusion>" 70) 
  where "Fusion N M p x = (case p of (p1,p2) \<Rightarrow> case x of (x1,x2) \<Rightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2))"

lemma [simp]: "(p1,p2) \<nuLinkL> N \<nuFusion> M \<nuLinkR> (x1,x2) \<longleftrightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)" unfolding Fusion_def Refining_ex by simp
lemma [elim,\<nu>elim]: "(x1,x2) \<ratio> N1 \<nuFusion> N2 \<Longrightarrow> (x1 \<ratio> N1 \<Longrightarrow> x2 \<ratio> N2 \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by simp

lemma [\<nu>intro]: "\<nu>Share N s1 f1 \<Longrightarrow> \<nu>Share M s2 f2 \<Longrightarrow> \<nu>Share (N \<nuFusion> M) (s1 \<times>\<^sub>p s2) (\<lambda>z. map_prod (f1 z) (f2 z))" unfolding \<nu>Share_def by auto
lemma [\<nu>intro]: "\<nu>CEqual N P eq1 \<Longrightarrow> \<nu>CEqual M Q eq2 \<Longrightarrow> \<nu>CEqual (N \<nuFusion> M) (P \<times>\<^sub>r Q) (eq1 \<times>\<^sub>r eq2)"unfolding \<nu>CEqual_def pair_forall by auto
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>y \<tycolon> Y\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>(x,y) \<tycolon> X \<nuFusion> Y\<tort_rbrace>" unfolding \<nu>Disposable_def pair_forall by auto
lemma [\<nu>intro]: "\<nu>ShrIdentical N sid1 \<Longrightarrow> \<nu>ShrIdentical M sid2 \<Longrightarrow> \<nu>ShrIdentical (N \<nuFusion> M) (sid1 \<times>\<^sub>r sid2)" unfolding \<nu>ShrIdentical_def by (auto 0 4)
lemma [\<nu>intro]: "\<nu>Ownership N ow1 \<Longrightarrow> \<nu>Ownership M ow2 \<Longrightarrow> \<nu>Ownership (N \<nuFusion> M) (ow1 \<times>\<^sub>o\<^sub>w ow2)" unfolding \<nu>Ownership_def by simp
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
definition llty_tuple :: " 'a tuple itself \<Rightarrow> llty " where [simp]: "llty_tuple _ = la_tup (llty TYPE('a))"
definition disposable_tuple :: " 'a tuple \<Rightarrow> bool " where "disposable_tuple = pred_tuple disposable"
lemma [simp]: "disposable (Tuple x) = disposable x" unfolding disposable_tuple_def by simp
instance by standard
end

subsubsection \<open>zero\<close>

instantiation tuple :: ("{zero,field_list}") zero begin
definition zero_tuple :: " 'a tuple " where [simp]: "zero_tuple = Tuple 0"
instance by standard
end

subsubsection \<open>shareable\<close>

instantiation tuple :: ("{ownership,field_list}") ownership begin
definition ownership_tuple :: " 'a tuple \<Rightarrow> ownership" where "ownership_tuple = case_tuple ownership"
lemma [simp]: "ownership (Tuple a) = ownership a" unfolding ownership_tuple_def by simp
instance by standard
end

instantiation tuple :: ("{sharing_identical,field_list}") sharing_identical begin
definition sharing_identical_tuple :: " 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> bool " where "sharing_identical_tuple = rel_tuple sharing_identical"
lemma [simp]: "sharing_identical (Tuple a) (Tuple b) \<longleftrightarrow> sharing_identical a b" unfolding sharing_identical_tuple_def by simp
instance proof
  fix x y z :: " 'a tuple"  and a b :: zint
  show "sharing_identical x x" by (cases x) simp
  show "sharing_identical x y = sharing_identical y x" by (cases x, cases y) simp
  show "sharing_identical x y \<Longrightarrow> sharing_identical y z \<Longrightarrow> sharing_identical x z" by (cases x, cases y, cases z) (auto intro: sharing_identical_trans)
qed
end

instantiation tuple :: ("{share,field_list}") share begin
definition shareable_tuple :: " 'a tuple \<Rightarrow> bool " where [simp]: "shareable_tuple = pred_tuple shareable"
definition share_tuple :: " zint \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple " where [simp]: "share_tuple z = map_tuple (share z)"
definition dpriv_tuple :: " 'a tuple \<Rightarrow> 'a tuple " where "dpriv_tuple = map_tuple dpriv"
lemma [simp]: "shareable (Tuple x) = shareable x" unfolding shareable_tuple_def by simp
lemma [simp]: "share z (Tuple x) = Tuple (share z x)" unfolding share_tuple_def by simp
lemma [simp]: "dpriv (Tuple a) = Tuple (dpriv a)" unfolding dpriv_tuple_def by simp
instance proof
  fix x y z :: " 'a tuple"  and a b :: zint
  show "share (Gi 0) x = x" by (cases x) auto
  show "share b (share a x) = share (a + b) x" by (cases x) auto
qed
end

subsubsection \<open>ceq\<close>

instantiation tuple :: ("{ceq,field_list}") ceq begin
definition ceqable_tuple :: " 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> bool " where "ceqable_tuple = rel_tuple ceqable"
definition ceq_tuple :: " 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> bool " where "ceq_tuple = rel_tuple ceq"
lemma [simp]: "ceqable (Tuple a) (Tuple b) = ceqable a b" unfolding ceqable_tuple_def by simp
lemma [simp]: "ceq (Tuple a) (Tuple b) = ceq a b" unfolding ceq_tuple_def by simp
instance proof
  fix x y z :: " 'a tuple"
  show "ceqable x y = ceqable y x" by (cases x; cases y) simp
  show "ceqable x x \<Longrightarrow> ceq x x" by (cases x) auto
  show "ceqable x y \<Longrightarrow> ceq x y = ceq y x" by (cases x; cases y) simp
  show "ceqable x y \<Longrightarrow> ceqable y z \<Longrightarrow> ceqable x z \<Longrightarrow> ceq x y \<Longrightarrow> ceq y z \<Longrightarrow> ceq x z" by (cases x, cases y, cases z) (simp, blast intro: ceq_trans)
qed
end

subsubsection \<open>naive\<close>

instantiation tuple :: ("{naive_lrep,field_list}") naive_lrep begin
instance proof
  fix x y :: " 'a tuple " and z :: zint
  show "disposable x = True" by (cases x) simp
  show "shareable x = True" by (cases x) simp
  show "dpriv x = x" by (cases x) simp
  show " share z x = x" by (cases x) simp
  show " sharing_identical x y = True" by (cases x; cases y) simp
qed
end

subsubsection \<open>miscellaneous\<close>

instantiation tuple :: (field_list) field begin instance by standard end
instantiation tuple :: (field_list) field_list begin instance by standard end

subsection \<open>Nu abstraction - `NuTuple`\<close>

definition NuTuple :: "(('a::field_list), 'b) nu \<Rightarrow> ('a tuple, 'b) nu" ("\<lbrace> _ \<rbrace>") where "\<lbrace> N \<rbrace> p x = (case p of Tuple p' \<Rightarrow> p' \<nuLinkL> N \<nuLinkR> x)"

lemma [simp]: "Tuple p \<nuLinkL> \<lbrace> N \<rbrace> \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> N \<nuLinkR> x" unfolding NuTuple_def Refining_ex by simp
lemma [elim,\<nu>elim]: "x \<ratio> \<lbrace> N \<rbrace> \<Longrightarrow> (x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def tuple_exists by simp

lemma [\<nu>intro]: "\<nu>Share N s f \<Longrightarrow> \<nu>Share \<lbrace> N \<rbrace> s f" unfolding \<nu>Share_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>CEqual N P eq \<Longrightarrow> \<nu>CEqual \<lbrace> N \<rbrace> P eq" unfolding \<nu>CEqual_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>x \<tycolon> \<lbrace> X \<rbrace>\<tort_rbrace>" unfolding \<nu>Disposable_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>ShrIdentical N sid \<Longrightarrow> \<nu>ShrIdentical \<lbrace> N \<rbrace> sid" unfolding \<nu>ShrIdentical_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>Ownership N ow \<Longrightarrow> \<nu>Ownership \<lbrace> N \<rbrace> ow" unfolding \<nu>Ownership_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>Zero N z \<Longrightarrow> \<nu>Zero \<lbrace> N \<rbrace> z" unfolding \<nu>Zero_def by simp

section \<open>Memory Witness\<close>

datatype ('a::field) memcon = memcon memadr \<open>('a::field) list\<close>
type_synonym 'a memobj = " 'a memcon owning"

lemma memcon_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (memcon a x))" by (metis memcon.exhaust) 
lemma memcon_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (memcon a x))" by (metis memcon.exhaust) 


subsection \<open>Instantiations\<close>

instantiation memcon :: (field) disposable begin
definition disposable_memcon :: " 'a memcon \<Rightarrow> bool" where [simp]: "disposable_memcon _ = False"
instance by standard
end

instantiation memcon :: ("{ownership, field}") ownership begin
definition ownership_memcon :: " 'a memcon \<Rightarrow> ownership"
  where "ownership_memcon x = (case x of memcon _ y \<Rightarrow> OWS_L (map ownership y))"
lemma [simp]: "ownership (memcon p x) = OWS_L (map ownership x)"
  unfolding ownership_memcon_def by simp
instance by standard
end

instantiation memcon :: ( "{sharing_identical,ownership, field}") sharing_identical begin
definition sharing_identical_memcon :: "  'a memcon \<Rightarrow> 'a memcon \<Rightarrow> bool"
  where "sharing_identical_memcon = rel_memcon (inv_imagep (=) ownership)"
lemma [simp]: "sharing_identical (memcon pa a) (memcon pb b) \<longleftrightarrow> (pa = pb) \<and> list_all2 (inv_imagep (=) ownership) a b"
  unfolding sharing_identical_memcon_def by auto
instance proof
  fix x y z :: " 'a memcon"
  show "sharing_identical x x" by (cases x, simp, rule list_all2_refl) simp
  show "sharing_identical x y = sharing_identical y x" by (cases x; cases y; simp add: list_all2_conv_all_nth) auto
  show "sharing_identical x y \<Longrightarrow> sharing_identical y z \<Longrightarrow> sharing_identical x z"
    by (cases x; cases y; cases z; simp add: list_all2_conv_all_nth)
qed
end

subsection \<open>Image: object\<close>

datatype 'a object = object memadr 'a (infixr "\<R_arr_tail>" 60)

abbreviation "adr_of_object obj \<equiv> (case obj of a \<R_arr_tail> x \<Rightarrow> a)"
abbreviation "x_of_object obj \<equiv> (case obj of a \<R_arr_tail> x \<Rightarrow> x)"

lemma object_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)

subsection \<open>\<nu>-abstraction : Slice\<close>

definition MemSlice :: "(('a::field), 'b) nu \<Rightarrow> ('a memobj, 'b list object owning) nu"
  where "MemSlice N p x = (
    case (p,x) of (zp \<left_fish_tail> memcon adrp p , z \<left_fish_tail> (adrx \<R_arr_tail> x)) \<Rightarrow>
        (zp = z) \<and> (adrp = adrx) \<and> list_all2 (\<lambda>p x. p \<nuLinkL> N \<nuLinkR> x) p x \<and> within_seg (length x) adrx
    | (\<down_fish_tail> , \<down_fish_tail>) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma [simp]: "zp \<left_fish_tail> memcon adrp p \<nuLinkL> MemSlice N \<nuLinkR> z \<left_fish_tail> adrx \<R_arr_tail> x \<longleftrightarrow>
    (zp = z) \<and> (adrp = adrx) \<and> list_all2 (\<lambda>p x. p \<nuLinkL> N \<nuLinkR> x) p x \<and> within_seg (length x) adrx"
  and [simp]: "\<down_fish_tail> \<nuLinkL> MemSlice N \<nuLinkR> x' \<longleftrightarrow> x' = \<down_fish_tail>" and [simp]: "p' \<nuLinkL> MemSlice N \<nuLinkR> \<down_fish_tail> \<longleftrightarrow> p' = \<down_fish_tail>"
  unfolding MemSlice_def Refining_ex by (auto simp add: memptr_forall split: memcon.split owning.split)

lemma [elim,\<nu>elim]: "z \<left_fish_tail> a \<R_arr_tail> xs \<ratio> MemSlice N \<Longrightarrow>
    (within_seg (length xs) a \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> xs ! i \<ratio> N) \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding Inhabited_def apply (auto 6 6 simp add: lrep_exps list_all2_conv_all_nth) by blast 

lemma [\<nu>intro]: "\<nu>Share (MemSlice N) (\<lambda>x. True) share"
  unfolding \<nu>Share_def by (simp add: owning_forall memcon_forall memptr_forall object_forall)
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>\<down_fish_tail> \<tycolon> MemSlice N\<tort_rbrace>" unfolding \<nu>Disposable_def by simp
lemma [\<nu>intro]: "\<nu>CEqual (MemSlice N) (\<lambda>x y. True) (\<lambda>x y. True)" unfolding \<nu>CEqual_def by simp
lemma [\<nu>intro]: "\<nu>Ownership (MemSlice N) ownership"
  unfolding \<nu>Ownership_def by (simp add: owning_forall memcon_forall memptr_forall object_exists)
lemma [\<nu>intro]: "\<nu>Ownership N ow \<Longrightarrow> \<nu>ShrIdentical (MemSlice N) (rel_owning (rel_object (list_all2 (inv_imagep (=) ow))))"
  unfolding \<nu>Ownership_def \<nu>ShrIdentical_def
  by (simp add: lrep_exps list_all2_conv_all_nth) (auto 0 3)
lemma [\<nu>intro]: "\<nu>Zero (MemSlice N) \<down_fish_tail>" unfolding \<nu>Zero_def by simp

section \<open>Ghost\<close>

datatype 'a ghost = ghost 'a

lemma ghost_forall[lrep_exps]: "All P \<longleftrightarrow> (\<forall>x. P (ghost x))" by (metis ghost.exhaust)
lemma ghost_exists[lrep_exps]: "Ex P \<longleftrightarrow> (\<exists>x. P (ghost x))" by (metis ghost.exhaust)

subsection \<open>Instantiations\<close>

instantiation ghost :: (type) field begin
definition llty_ghost :: " 'a ghost itself \<Rightarrow> llty" where [simp]: "llty_ghost _ = la_z"
definition disposable_ghost :: " 'a ghost \<Rightarrow> bool " where [simp]: "disposable_ghost _ = True"
instance by standard
end

lemma [\<nu>intro]: "\<nu>Disposable S" for S :: " 'a ghost set " unfolding \<nu>Disposable_def by simp

instantiation ghost :: (type) field_list begin instance by standard end

instantiation ghost :: (type) ceq begin
definition ceqable_ghost :: " 'a ghost \<Rightarrow> 'a ghost \<Rightarrow> bool" where [simp]: "ceqable_ghost _ _ = True"
definition ceq_ghost :: " 'a ghost \<Rightarrow> 'a ghost \<Rightarrow> bool" where [simp]: "ceq_ghost _ _ = True"
instance by standard auto
end

instantiation ghost :: (type) sharing_identical begin
definition sharing_identical_ghost :: "'a ghost \<Rightarrow> 'a ghost \<Rightarrow> bool" where [simp]: "sharing_identical_ghost _ _ = True"
instance by standard auto
end

instantiation ghost :: (type) share begin
definition shareable_ghost :: "'a ghost \<Rightarrow> bool" where [simp]: "shareable_ghost _ = True"
definition share_ghost :: "zint \<Rightarrow> 'a ghost \<Rightarrow> 'a ghost" where [simp]: "share_ghost _ x = x"
definition dpriv_ghost :: "'a ghost \<Rightarrow> 'a ghost" where [simp]: "dpriv_ghost x = x"
instance by standard auto
end

instantiation ghost :: (type) ownership begin
definition ownership_ghost :: " 'a ghost \<Rightarrow> ownership" where [simp]: "ownership_ghost _ = OWS_0"
instance by standard
end

lemma [\<nu>intro]: "\<nu>Ownership N (\<lambda>_. OWS_0)" for N :: "('a ghost, 'b) nu" unfolding \<nu>Ownership_def by simp

instantiation ghost :: (zero) zero begin
definition zero_ghost :: " 'a ghost" where [simp]: "zero_ghost = ghost 0"
instance by standard
end

subsubsection \<open>\<nu>-abstraction\<close>

definition Ghost :: "('a ghost, 'a) nu" where "Ghost p x \<longleftrightarrow> (case p of ghost p' \<Rightarrow> p' = x)"

lemma [simp]: "ghost p \<nuLinkL> Ghost \<nuLinkR> x \<longleftrightarrow> p = x" unfolding Ghost_def Refining_ex by auto

lemma [\<nu>intro]: "\<nu>Share Ghost (\<lambda>x. True) (\<lambda>z x. x)" unfolding \<nu>Share_def by simp
lemma [\<nu>intro]: "\<nu>ShrIdentical Ghost (\<lambda>_ _. True)" unfolding \<nu>ShrIdentical_def by simp
lemma [\<nu>intro]: "\<nu>CEqual Ghost (\<lambda>_ _. True) (\<lambda>_ _. True)" unfolding \<nu>CEqual_def by simp
lemma [\<nu>intro]: "\<nu>Deprive Ghost (\<lambda>x. x)" unfolding \<nu>Deprive_def by simp
lemma [\<nu>intro]: "\<nu>Zero Ghost 0" unfolding \<nu>Zero_def by simp

(* definition MemObj :: "(('a::field), 'b) nu \<Rightarrow> ('a memobj, 'b object owning) nu"
  where "MemObj N p x = (
    case (p,x) of (zp \<left_fish_tail> memcon adrp p , z \<left_fish_tail> (adrx \<R_arr_tail> x)) \<Rightarrow> (zp = z) \<and> (adrp = adrx) \<and> (p \<nuLinkL> N \<nuLinkR> x)
        | (\<down_fish_tail> , \<down_fish_tail>) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma [simp]: "zp \<left_fish_tail> memcon adrp p \<nuLinkL> MemObj N \<nuLinkR> z \<left_fish_tail> adrx \<R_arr_tail> x \<longleftrightarrow> (zp = z) \<and> (adrp = adrx) \<and> (p \<nuLinkL> N \<nuLinkR> x)"
  and [simp]: "\<down_fish_tail> \<nuLinkL> MemObj N \<nuLinkR> x' \<longleftrightarrow> x' = \<down_fish_tail>" and [simp]: "p' \<nuLinkL> MemObj N \<nuLinkR> \<down_fish_tail> \<longleftrightarrow> p' = \<down_fish_tail>"
  unfolding MemObj_def Refining_ex by  (auto simp add: memptr_forall split: memcon.split owning.split)

lemma [\<nu>intro]: "\<nu>Share (MemObj N) (\<lambda>x. True) share"
  unfolding \<nu>Share_def by (simp add: owning_forall memcon_forall memptr_forall object_forall)
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>\<down_fish_tail> \<tycolon> MemObj N\<tort_rbrace>" unfolding \<nu>Disposable_def by simp
lemma [\<nu>intro]: "\<nu>CEqual (MemObj N) (\<lambda>x y. True) (\<lambda>x y. True)" unfolding \<nu>CEqual_def by simp
lemma [\<nu>intro]: "\<nu>Ownership (MemObj N) ownership"
  unfolding \<nu>Ownership_def by (simp add: owning_forall memcon_forall memptr_forall object_exists)
lemma [\<nu>intro]: "\<nu>Ownership N ow \<Longrightarrow> \<nu>ShrIdentical (MemObj N) (rel_owning (rel_object (inv_imagep (=) ow)))"
  unfolding \<nu>Ownership_def \<nu>ShrIdentical_def
  by (simp add: owning_forall memcon_forall memptr_forall object_exists owning_exists) auto
lemma [\<nu>intro]: "\<nu>Zero (MemObj N) \<down_fish_tail>" unfolding \<nu>Zero_def by simp
*)

end