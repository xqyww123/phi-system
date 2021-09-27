theory NuLLReps
  imports NuPrim  "HOL-Library.Word"
  abbrevs "<own>" = "\<left_fish_tail>"
    and "<none>" = "\<down_fish_tail>"
    and "<object>" = "\<R_arr_tail>"
begin

text \<open>Semantic data representations\<close>

section \<open>Preliminary notions\<close>

datatype identity = idhypen identity nat (infixl "\<hyphen>" 70) | ID_MEM | ID_CONST string
  \<comment> \<open>A tree-like structure allowing infinite sub identity space, like folders where infinite sub-folders can be allocated\<close>

class field = lrep
class field_list = lrep

section \<open>The construction state\<close>

instantiation state :: (lrep) lrep begin
definition llty_state :: "'a state itself \<Rightarrow> llty" where [simp]: "llty_state _ = la_z"
instance by standard
end

section \<open>Owning\<close>

datatype 'a owning = Owning zint 'a (infix "\<left_fish_tail>" 60) | OwnNone ("\<down_fish_tail>")
  \<comment> \<open>\<^term>\<open>quantity_of_ownership \<left_fish_tail> data\<close>\<close>

lemma owning_forall: "All P \<longleftrightarrow> P \<down_fish_tail> \<and> (\<forall>z x. P (z \<left_fish_tail> x))" by (metis owning.exhaust) 
lemma owning_exists: "Ex P \<longleftrightarrow> P \<down_fish_tail> \<or> (\<exists>z x. P (z \<left_fish_tail> x))" by (metis owning.exhaust) 

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

subsection \<open>Nu abstractions\<close>

section \<open>Memory address\<close>

datatype ('spc::len) memadr = memadr identity  \<comment> \<open>'spc : address space\<close>
translations "id" <= "CONST memadr 0 id"

lemma memadr_exisits: "Ex P \<longleftrightarrow> (\<exists>id. P (memadr id))" by (metis memadr.exhaust) 
lemma memadr_forall: "All P \<longleftrightarrow> (\<forall>id. P (memadr id))" by (metis memadr.exhaust) 

subsection \<open>Instantiations\<close>

instantiation memadr :: (len) lrep begin
definition disposable_memadr :: "'a memadr \<Rightarrow> bool" where [simp]: "disposable_memadr _ = True"
definition llty_memadr :: "'a memadr itself \<Rightarrow> llty" where [simp]: "llty_memadr _ = la_p LENGTH('a)"
instance by standard
end

instantiation memadr :: (len) field begin instance by standard end

instantiation memadr :: (len) sharing_identical begin
definition sharing_identical_memadr :: " 'a memadr \<Rightarrow> 'a memadr \<Rightarrow> bool" where [simp]: "sharing_identical_memadr _ _ = True"
definition ownership_memadr :: " 'a memadr \<Rightarrow> ownership" where [simp]: "ownership_memadr _ = OWS_0"
instance by standard auto
end

instantiation memadr :: (len) share begin
definition shareable_memadr :: " 'a memadr \<Rightarrow> bool" where [simp]: "shareable_memadr _ = True"
definition share_memadr :: "zint \<Rightarrow> 'a memadr \<Rightarrow> 'a memadr" where [simp]: "share_memadr z x = x"
definition dpriv_memadr :: "'a memadr \<Rightarrow> 'a memadr" where [simp]: "dpriv_memadr x = x"
instance by standard auto
end

instantiation memadr :: (len) naive_lrep begin
instance by standard auto
end

section \<open>Void\<close>

instantiation void :: naive_lrep begin
definition share_void :: "zint \<Rightarrow> void \<Rightarrow> void" where [simp]: "share_void z = id"
definition shareable_void :: "void \<Rightarrow> bool" where [simp]: "shareable_void _ = True"
definition sharing_identical_void :: "void \<Rightarrow> void \<Rightarrow> bool" where [simp]: "sharing_identical_void x y = True"
definition dpriv_void :: "void \<Rightarrow> void" where [simp]: "dpriv_void x = x"
instance by standard auto
end

instantiation void :: field_list begin instance by standard end

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
definition ownership_word :: " 'a word \<Rightarrow> ownership" where [simp]: "ownership_word _ = OWS_0"
instance by standard auto
end

instantiation word :: (len) zero_lrep
begin
definition [simp]: "lty_zero_word = (0 :: 'a word)"
instance by standard
end

instantiation word :: (len) ceq
begin
definition ceqable_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where [simp]: "ceqable_word x y = True"
definition ceq_word :: "'a word \<Rightarrow>  'a word \<Rightarrow> bool" where [simp]: "ceq_word x y = (x = y)"
instance by standard (auto+)
end

instantiation word :: (len) field begin instance by standard end

subsection \<open>Basic \<nu>-abstractions based on integer type\<close>

subsubsection \<open>Natural number\<close>

definition NuNat :: "('a::len) itself \<Rightarrow> ('a word, nat) nu"
  where "NuNat _ = Nu (\<lambda>px. case px of (p,x) \<Rightarrow> (unat p = x))"
syntax "_NuNat_" :: "type \<Rightarrow> logic" (\<open>\<nat>'[_']\<close>)
translations "\<nat>['x]" == "CONST NuNat (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuNat b \<nuLinkR> x \<equiv> (unat p = x)" unfolding NuNat_def by auto
lemma [\<nu>intro]: "\<nu>CEqual (NuNat b) (\<lambda>x y. True) (=)"
  unfolding \<nu>CEqual_def NuNat_def by (auto simp add: unsigned_word_eqI)

definition NuNatRound :: "('a::len) itself \<Rightarrow> ('a word, nat) nu"
  where "NuNatRound _ = Nu (\<lambda>px. case px of (p,x) \<Rightarrow> (p = of_nat x))"
syntax "_NuNatRound_" :: "type \<Rightarrow> logic" (\<open>\<nat>\<^sup>r'[_']\<close>)
translations "\<nat>\<^sup>r['x]" == "CONST NuNatRound (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuNatRound b \<nuLinkR> x \<equiv> (p = of_nat x)" unfolding NuNatRound_def by auto

subsubsection \<open>Boolean\<close>

lemma [simp]: "(x \<noteq> 1) = (x = 0)" for x :: "1 word" proof -
  have "(UNIV:: 1 word set) = {0,1}" unfolding UNIV_word_eq_word_of_nat
  using less_2_cases apply auto apply force
  by (metis UNIV_I UNIV_word_eq_word_of_nat len_num1 power_one_right)
  then show ?thesis  by auto
qed

definition NuBool :: "(1 word, bool) nu" ("\<bool>")
  where "NuBool = Nu (\<lambda>px. case px of (p,x) \<Rightarrow> (p = 1) = x)"
lemma [simp]: "p \<nuLinkL> \<bool> \<nuLinkR> x \<longleftrightarrow> (p = 1) = x" unfolding NuBool_def by simp
lemma [\<nu>intro]: "\<nu>CEqual \<bool> (\<lambda>x y. True)  (=)" unfolding \<nu>CEqual_def NuBool_def by auto


section \<open>Prod & the pair abstract structure\<close>

subsection \<open>Lrep instantiations\<close>

instantiation prod :: (field, field_list) field_list begin instance by standard end

instantiation prod :: (zero_lrep, zero_lrep) zero_lrep begin
definition lty_zero_prod :: "'a \<times> 'b" where [simp]: "lty_zero_prod = (lty_zero,lty_zero)"
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
  where "Fusion N M = Nu (\<lambda>px. case px of ((p1,p2),(x1,x2)) \<Rightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2))"

lemma [simp]: "(p1,p2) \<nuLinkL> N \<nuFusion> M \<nuLinkR> (x1,x2) \<longleftrightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)" unfolding Fusion_def by simp
lemma [elim]: "(x1,x2) \<ratio> N1 \<nuFusion> N2 \<Longrightarrow> (x1 \<ratio> N1 \<Longrightarrow> x2 \<ratio> N2 \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def by simp

lemma [\<nu>intro]: "\<nu>Share N s1 f1 \<Longrightarrow> \<nu>Share M s2 f2 \<Longrightarrow> \<nu>Share (N \<nuFusion> M) (s1 \<times>\<^sub>p s2) (\<lambda>z. map_prod (f1 z) (f2 z))" unfolding \<nu>Share_def by auto
lemma [\<nu>intro]: "\<nu>CEqual N P eq1 \<Longrightarrow> \<nu>CEqual M Q eq2 \<Longrightarrow> \<nu>CEqual (N \<nuFusion> M) (P \<times>\<^sub>r Q) (eq1 \<times>\<^sub>r eq2)"unfolding \<nu>CEqual_def pair_forall by auto
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>y \<tycolon> Y\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>(x,y) \<tycolon> X \<nuFusion> Y\<tort_rbrace>" unfolding \<nu>Disposable_def pair_forall by auto
lemma [\<nu>intro]: "\<nu>ShrIdentical N sid1 \<Longrightarrow> \<nu>ShrIdentical M sid2 \<Longrightarrow> \<nu>ShrIdentical (N \<nuFusion> M) (sid1 \<times>\<^sub>r sid2)" unfolding \<nu>ShrIdentical_def by (auto 0 4)

section \<open>Tuple\<close>

datatype 'a tuple = Tuple "('a::field_list)"

lemma tuple_exists: "Ex P \<longleftrightarrow> (\<exists>x. P (Tuple x))" by (metis tuple.exhaust) 
lemma tuple_forall: "All P \<longleftrightarrow> (\<forall>x. P (Tuple x))" by (metis tuple.exhaust) 

subsection \<open>Lrep instantiations\<close>

subsubsection \<open>lrep\<close>

instantiation tuple :: (field_list) lrep begin
definition llty_tuple :: " 'a tuple itself \<Rightarrow> llty " where [simp]: "llty_tuple _ = la_tup (llty TYPE('a))"
definition disposable_tuple :: " 'a tuple \<Rightarrow> bool " where "disposable_tuple = pred_tuple disposable"
lemma [simp]: "disposable (Tuple x) = disposable x" unfolding disposable_tuple_def by simp
instance by standard
end

subsubsection \<open>zero\<close>

instantiation tuple :: ("{zero_lrep,field_list}") zero_lrep begin
definition lty_zero_tuple :: " 'a tuple " where [simp]: "lty_zero_tuple = Tuple lty_zero"
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

subsection \<open>Nu abstraction - `NuTuple`\<close>

definition NuTuple :: "(('a::field_list), 'b) nu \<Rightarrow> ('a tuple, 'b) nu" ("\<lbrace> _ \<rbrace>")
  where "\<lbrace> N \<rbrace> = Nu (\<lambda>(p,x). case p of Tuple p' \<Rightarrow> p' \<nuLinkL> N \<nuLinkR> x)"

lemma [simp]: "Tuple p \<nuLinkL> \<lbrace> N \<rbrace> \<nuLinkR> x \<longleftrightarrow> p \<nuLinkL> N \<nuLinkR> x" unfolding NuTuple_def by simp
lemma [elim]: "x \<ratio> \<lbrace> N \<rbrace> \<Longrightarrow> (x \<ratio> N \<Longrightarrow> C) \<Longrightarrow> C" unfolding Inhabited_def tuple_exists by simp

lemma [\<nu>intro]: "\<nu>Share N s f \<Longrightarrow> \<nu>Share \<lbrace> N \<rbrace> s f" unfolding \<nu>Share_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>CEqual N P eq \<Longrightarrow> \<nu>CEqual \<lbrace> N \<rbrace> P eq" unfolding \<nu>CEqual_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>x \<tycolon> \<lbrace> X \<rbrace>\<tort_rbrace>" unfolding \<nu>Disposable_def tuple_forall by simp
lemma [\<nu>intro]: "\<nu>ShrIdentical N sid \<Longrightarrow> \<nu>ShrIdentical \<lbrace> N \<rbrace> sid" unfolding \<nu>ShrIdentical_def tuple_forall by simp

section \<open>Memory Witness\<close>

datatype ('len::len, 'a::field) memcon = memcon \<open>('len::len) memadr\<close> \<open>'a::field\<close>
type_synonym ('len,'a) memobj = " ('len,'a) memcon owning"

lemma memcon_forall: "All P \<longleftrightarrow> (\<forall>a x. P (memcon a x))" by (metis memcon.exhaust) 
lemma memcon_exists: "Ex P \<longleftrightarrow> (\<exists>a x. P (memcon a x))" by (metis memcon.exhaust) 


subsection \<open>Instantiations\<close>

instantiation memcon :: (len,field) disposable begin
definition disposable_memcon :: " ('a,'b) memcon \<Rightarrow> bool" where [simp]: "disposable_memcon _ = False"
instance by standard
end

instantiation memcon :: ("len", "{ownership, field}") ownership begin
definition ownership_memcon :: " ('a,'b) memcon \<Rightarrow> ownership"
  where "ownership_memcon x = (case x of memcon _ y \<Rightarrow> ownership y)"
lemma [simp]: "ownership (memcon p x) = ownership x"
  unfolding ownership_memcon_def by simp
instance by standard
end

instantiation memcon :: ("len", "{sharing_identical,ownership, field}") sharing_identical begin
definition sharing_identical_memcon :: "  ('a,'b) memcon \<Rightarrow> ('a,'b) memcon \<Rightarrow> bool"
  where "sharing_identical_memcon = rel_memcon (=) (inv_imagep (=) ownership)"
lemma [simp]: "sharing_identical (memcon pa a) (memcon pb b) \<longleftrightarrow> (pa = pb) \<and> (ownership a = ownership b)"
  unfolding sharing_identical_memcon_def by (cases pa; cases pb) simp
instance proof
  fix x y z :: " ('a,'b) memcon"
  show "sharing_identical x x" by (cases x) simp
  show "sharing_identical x y = sharing_identical y x" by (cases x; cases y) auto
  show "sharing_identical x y \<Longrightarrow> sharing_identical y z \<Longrightarrow> sharing_identical x z" by (cases x; cases y; cases z) auto
qed
end

subsection \<open>\<nu>-abstraction\<close>

datatype 'a object = object identity 'a (infix "\<R_arr_tail>" 62)

lemma object_forall: "All P \<longleftrightarrow> (\<forall>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)
lemma object_exists: "Ex P \<longleftrightarrow> (\<exists>a x. P (a \<R_arr_tail> x))" by (metis object.exhaust)


definition MemObj :: "(('a::field), 'b) nu \<Rightarrow> ((('len::len),'a) memobj, 'b object owning) nu"
  where "MemObj N = Nu (\<lambda>px.
    case px of (zp \<left_fish_tail> memcon (memadr adrp) p , z \<left_fish_tail> (adrx \<R_arr_tail> x)) \<Rightarrow> (zp = z) \<and> (adrp = adrx) \<and> (p \<nuLinkL> N \<nuLinkR> x)
        | (\<down_fish_tail> , \<down_fish_tail>) \<Rightarrow> True | _ \<Rightarrow> False)"  

lemma [simp]: "zp \<left_fish_tail> memcon (memadr  adrp) p \<nuLinkL> MemObj N \<nuLinkR> z \<left_fish_tail> adrx \<R_arr_tail> x \<longleftrightarrow> (zp = z) \<and> (adrp = adrx) \<and> (p \<nuLinkL> N \<nuLinkR> x)"
  and [simp]: "\<down_fish_tail> \<nuLinkL> MemObj N \<nuLinkR> x' \<longleftrightarrow> x' = \<down_fish_tail>" and [simp]: "p' \<nuLinkL> MemObj N \<nuLinkR> \<down_fish_tail> \<longleftrightarrow> p' = \<down_fish_tail>"
  unfolding MemObj_def by  (auto simp add: memadr_forall split: memcon.split owning.split)

lemma [\<nu>intro]: "\<nu>Share (MemObj N) (\<lambda>x. True) share"
  unfolding \<nu>Share_def by (simp add: owning_forall memcon_forall memadr_forall object_forall)
lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>\<down_fish_tail> \<tycolon> MemObj N\<tort_rbrace>" unfolding \<nu>Disposable_def by simp
lemma [\<nu>intro]: "\<nu>CEqual (MemObj N) (\<lambda>x y. True) (\<lambda>x y. True)" unfolding \<nu>CEqual_def by simp
lemma [\<nu>intro]: "\<nu>Ownership (MemObj N) ownership"
  unfolding \<nu>Ownership_def by (simp add: owning_forall memcon_forall memadr_forall object_exists)
lemma [\<nu>intro]: "\<nu>Ownership N ow \<Longrightarrow> \<nu>ShrIdentical (MemObj N) (rel_owning (rel_object (inv_imagep (=) ow)))"
  unfolding \<nu>Ownership_def \<nu>ShrIdentical_def
  by (simp add: owning_forall memcon_forall memadr_forall object_exists owning_exists) auto

end