theory NuLLReps
  imports NuPrim  "HOL-Library.Word"
begin

text \<open>Semantic data representations\<close>

section \<open>The construction state\<close>

instantiation state :: (lrep) lrep begin
definition llty_state :: "'a state itself \<Rightarrow> llty" where [simp]: "llty_state _ = la_z"
instance by standard
end

section \<open>Miscellaneous built-in\<close>

instantiation void :: naive_lrep begin
definition share_void :: "zint \<Rightarrow> void \<Rightarrow> void" where [simp]: "share_void z = id"
definition shareable_void :: "void set" where [simp]: "shareable_void = UNIV"
definition revert_void :: "void \<Rightarrow> void \<Rightarrow> bool" where [simp]: "revert_void x y = True"
definition dpriv_void :: "void \<Rightarrow> void" where [simp]: "dpriv_void x = x"
instance by standard auto
end


section \<open>The integer data type\<close>

subsection \<open>Lrep instantiations\<close>

instantiation word :: (len) naive_lrep
begin
definition llty_word :: "'a word itself \<Rightarrow> llty" where [simp]: "llty_word _ = la_i LENGTH('a)"
definition share_word :: "zint \<Rightarrow> 'a word \<Rightarrow> 'a word" where [simp]: "share_word z = id"
definition shareable_word :: "'a word set" where [simp]: "shareable_word = UNIV"
definition revert_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where [simp]: "revert_word x y = True"
definition dpriv_word :: "'a word \<Rightarrow> 'a word" where [simp]: "dpriv_word x = x"
definition disposable_word :: "'a word set" where [simp]: "disposable_word = UNIV"
instance by standard auto
end

instantiation word :: (len) zero_lrep
begin
definition [simp]: "lty_zero_word = (0 :: 'a word)"
instance by standard
end

instantiation word :: (len) ceq_lrep
begin
definition ceqable_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where [simp]: "ceqable_word x y = True"
definition ceq_word :: "'a word \<Rightarrow>  'a word \<Rightarrow> bool" where [simp]: "ceq_word x y = (x = y)"
instance by standard (auto+)
end

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


section \<open>The pair abstract structure\<close>

subsection \<open>Lrep instantiations\<close>

instantiation prod :: (zero_lrep, zero_lrep) zero_lrep begin
definition lty_zero_prod :: "'a \<times> 'b" where [simp]: "lty_zero_prod = (lty_zero,lty_zero)"
instance by standard
end

instantiation prod :: (sharable_lrep, sharable_lrep) sharable_lrep begin
definition revert_prod :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool"
  where "revert_prod v1 v2 \<longleftrightarrow> (case v1 of (a1,b1) \<Rightarrow> case v2 of (a2,b2) \<Rightarrow> revert a1 a2 \<and> revert b1 b2)"
lemma [simp]: "revert (a1,b1) (a2,b2) \<longleftrightarrow> revert a1 a2 \<and> revert b1 b2"
  unfolding revert_prod_def by simp
definition shareable_prod :: "('a \<times> 'b) set" where "shareable_prod = shareable \<times> shareable"
lemma [simp]: "(a,b) \<in> shareable \<longleftrightarrow> a \<in> shareable \<and> b \<in> shareable" unfolding shareable_prod_def by simp
definition share_prod :: "zint \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where [simp]: "share_prod z x = (case x of (a,b) \<Rightarrow> (share z a, share z b))"
definition dpriv_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where [simp]: "dpriv_prod x = (case x of (a,b) \<Rightarrow> (dpriv a, dpriv b))"
instance by standard (auto intro: revert_trans)
end

instantiation prod :: (naive_lrep, naive_lrep) naive_lrep
  begin instance by standard auto end

instantiation prod :: (ceq_lrep, ceq_lrep) ceq_lrep begin
definition ceqable_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  where "ceqable_prod x y = (case x of (a1,b1) \<Rightarrow> case y of (a2,b2) \<Rightarrow> ceqable a1 a2 \<and> ceqable b1 b2)"
lemma [simp]: "ceqable (a1,b1) (a2,b2) \<longleftrightarrow> ceqable a1 a2 \<and> ceqable b1 b2" unfolding ceqable_prod_def by auto
definition ceq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  where [simp]: "ceq_prod x y = (case x of (a1,b1) \<Rightarrow> case y of (a2,b2) \<Rightarrow> ceq a1 a2 \<and> ceq b1 b2)"
instance by standard (auto intro: ceq_trans)
end

subsection \<open>Fusion \<nu>-abstraction\<close>

definition Fusion :: "('a1::lrep,'b1) nu \<Rightarrow> ('a2::lrep,'b2) nu \<Rightarrow> ('a1 \<times> 'a2, 'b1 \<times> 'b2) nu" (infixr "\<nuFusion>" 70) 
  where "Fusion N M = Nu (\<lambda>px. case px of ((p1,p2),(x1,x2)) \<Rightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2))"
lemma Fusion_abst[simp]: "(p1,p2) \<nuLinkL> N \<nuFusion> M \<nuLinkR> (x1,x2) \<longleftrightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)"
  unfolding Fusion_def by simp
lemma "Inhabited \<tort_lbrace>(x1,x2) \<tycolon> N1 \<nuFusion> N2\<tort_rbrace> \<longleftrightarrow> Inhabited \<tort_lbrace>x1 \<tycolon> N1\<tort_rbrace> \<and> Inhabited \<tort_lbrace>x2 \<tycolon> N2\<tort_rbrace>"
  unfolding Inhabited_def by simp

lemma [\<nu>intro]: "\<nu>Share N s1 f1 \<Longrightarrow> \<nu>Share M s2 f2 \<Longrightarrow> \<nu>Share (N \<nuFusion> M) (s1 \<times> s2) (\<lambda>z x. case x of (x1,x2) \<Rightarrow> (f1 z x1, f2 z x2))"
  for N :: "('a :: sharable_lrep, 'b) nu" and M :: "('c :: sharable_lrep, 'd) nu" 
  unfolding \<nu>Share_def by auto
lemma [\<nu>intro]: "\<nu>CEqual N p \<Longrightarrow> \<nu>CEqual M q \<Longrightarrow> \<nu>CEqual (N \<nuFusion> M) (\<lambda>x. case x of ((a1,b1),(a2,b2)) \<Rightarrow> p (a1,a2) \<and> q (b1,b2))"
  unfolding \<nu>CEqual_def by auto

lemma [\<nu>intro]: "\<nu>Disposable \<tort_lbrace>x \<tycolon> X\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>y \<tycolon> Y\<tort_rbrace> \<Longrightarrow> \<nu>Disposable \<tort_lbrace>(x,y) \<tycolon> X \<nuFusion> Y\<tort_rbrace>"
  unfolding \<nu>Disposable_def by auto


section \<open>Tuple\<close>

class field = lrep
class field_list = lrep

instantiation void :: field_list begin instance by standard end
instantiation prod :: (field, field_list) field_list begin instance by standard end
instantiation word :: (len) field begin instance by standard end

datatype 'a tuple = Tuple "('a::field_list)"

subsection \<open>Lrep instantiations\<close>

instantiation tuple :: (field_list) lrep begin
definition llty_tuple :: " 'a tuple itself \<Rightarrow> llty " where [simp]: "llty_tuple _ = la_tup (llty TYPE('a))"
definition disposable_tuple :: " 'a tuple set " where [simp]: "disposable_tuple = image Tuple disposable"
instance by standard
end

instantiation tuple :: ("{zero_lrep,field_list}") zero_lrep begin
definition lty_zero_tuple :: " 'a tuple " where [simp]: "lty_zero_tuple = Tuple lty_zero"
instance by standard
end

instantiation tuple :: ("{sharable_lrep,field_list}") sharable_lrep begin
definition shareable_tuple :: " 'a tuple set " where [simp]: "shareable_tuple = image Tuple shareable"
definition share_tuple :: " zint \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple " where [simp]: "share_tuple z = map_tuple (share z)"
definition revert_tuple :: " 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> bool " where "revert_tuple x y = (case x of Tuple a \<Rightarrow> case y of Tuple b \<Rightarrow> revert a b)"
lemma [simp]: "revert (Tuple a) (Tuple b) \<longleftrightarrow> revert a b" unfolding revert_tuple_def by simp
definition dpriv_tuple :: " 'a tuple \<Rightarrow> 'a tuple " where "dpriv_tuple = map_tuple dpriv"
instance proof
  fix x y z :: " 'a tuple"  and a b :: zint
  show "revert x x" by (cases x) auto
  show "revert x y = revert y x" by (cases x, cases y) (auto simp add: revert_sym)
  show "revert x y \<Longrightarrow> revert y z \<Longrightarrow> revert x z" by (cases x, cases y, cases z) (auto intro: revert_trans)
  show "share (Gi 0) x = x" by (cases x) auto
  show "share b (share a x) = share (a + b) x" by (cases x) auto
qed
end

term "(O)"
instantiation tuple :: ("{ceq_lrep,field_list}") ceq_lrep begin

end
end