theory NuLLReps
  imports NuPrim  "HOL-Library.Word"
begin


  \<comment> \<open> StateOn stack registers
    where stack :: lrep and registers :: register_collection \<close>

instantiation state :: (lrep) lrep begin
definition llty_state :: "'a state itself \<Rightarrow> llty" where [simp]: "llty_state _ = la_z"
instance by standard
end

instantiation proc_ctx :: (lrep,register_collection) lrep begin
definition llty_proc_ctx :: "('a \<flower> 'r) itself \<Rightarrow> llty" where [simp]: "llty_proc_ctx _ = llty (TYPE ('a))"
instance by standard
end

instantiation word :: (len) naive_lrep
begin
definition llty_word :: "'a word itself \<Rightarrow> llty" where [simp]: "llty_word _ = la_i LENGTH('a)"
definition share_word :: "zint \<Rightarrow> 'a word \<Rightarrow> 'a word" where [simp]: "share_word z = id"
definition shareable_word :: "'a word set" where [simp]: "shareable_word = UNIV"
definition revert_word :: "'a word \<times> 'a word \<Rightarrow> bool" where [simp]: "revert_word xy = True"
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
definition ceqable_word :: "'a word \<times> 'a word \<Rightarrow> bool" where [simp]: "ceqable_word x = True"
definition ceq_word :: "'a word \<times> 'a word \<Rightarrow> bool" where [simp]: "ceq_word = (\<lambda>(x,y). (x = y))"
lemma ceq_word[simp]: "ceq (x,y) = (x = y)" for x :: "'a word" by simp
instance by standard (auto+)
end

instantiation prod :: (zero_lrep, zero_lrep) zero_lrep begin
definition lty_zero_prod :: "'a \<times> 'b" where [simp]: "lty_zero_prod = (lty_zero,lty_zero)"
instance by standard
end

instantiation prod :: (sharable_lrep, sharable_lrep) sharable_lrep begin
definition revert_prod :: "('a \<times> 'b) \<times> ('a \<times> 'b) \<Rightarrow> bool"
  where "revert_prod v \<longleftrightarrow> (case v of (v1,v2) \<Rightarrow> case v1 of (a1,b1) \<Rightarrow> case v2 of (a2,b2) \<Rightarrow> revert (a1,a2) \<and> revert (b1,b2))"
lemma [simp]: "revert (v1,v2) \<longleftrightarrow> (case v1 of (a1,b1) \<Rightarrow> case v2 of (a2,b2) \<Rightarrow> revert (a1,a2) \<and> revert (b1,b2))"
  unfolding revert_prod_def by simp
definition shareable_prod :: "('a \<times> 'b) set" where "shareable_prod = shareable \<times> shareable"
lemma [simp]: "(a,b) \<in> shareable \<longleftrightarrow> a \<in> shareable \<and> b \<in> shareable" unfolding shareable_prod_def by simp
definition share_prod :: "zint \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where [simp]: "share_prod z x = (case x of (a,b) \<Rightarrow> (share z a, share z b))"
definition dpriv_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where [simp]: "dpriv_prod x = (case x of (a,b) \<Rightarrow> (dpriv a, dpriv b))"
instance by standard (auto, (metis revert_sym revert_trans) +)
end

instantiation prod :: (naive_lrep, naive_lrep) naive_lrep
  begin instance by standard auto end

instantiation prod :: (ceq_lrep, ceq_lrep) ceq_lrep begin
definition ceqable_prod :: "('a \<times> 'b) \<times> 'a \<times> 'b \<Rightarrow> bool"
  where [simp]: "ceqable_prod x = (case x of ((a1,b1),(a2,b2)) \<Rightarrow> ceqable (a1,a2) \<and> ceqable (b1,b2))"
definition ceq_prod :: "('a \<times> 'b) \<times> 'a \<times> 'b \<Rightarrow> bool"
  where [simp]: "ceq_prod x = (case x of ((a1,b1),(a2,b2)) \<Rightarrow> ceq (a1,a2) \<and> ceq (b1,b2))"
instance by standard (auto simp add: ac_simps intro: ceq_trans)
end

definition NuNat :: "('a::len) itself \<Rightarrow> ('a word, nat) nu"
  where "NuNat _ = Nu (\<lambda>px. case px of (p,x) \<Rightarrow> (p = Word.of_nat x))"
syntax "_NuNat_" :: "type \<Rightarrow> logic" (\<open>\<nat>'[_']\<close>)
translations "\<nat>['x]" == "CONST NuNat (TYPE('x))" 

lemma [simp]: "p \<nuLinkL> NuNat b \<nuLinkR> x \<equiv> (p = Word.of_nat x)" unfolding NuNat_def by auto
lemma [\<nu>equable]: "\<nu>Equalable (NuNat b) (K True)" unfolding \<nu>Equalable_def NuNat_def by auto

definition NuBool :: "(1 word, bool) nu" ("\<bool>")
  where "NuBool = Nu (\<lambda>px. case px of (p,x) \<Rightarrow> (p = 1) = x)"
lemma [simp]: "p \<nuLinkL> \<bool> \<nuLinkR> x \<longleftrightarrow> (p = 1) = x" unfolding NuBool_def by simp
lemma [\<nu>equable]: "\<nu>Equalable \<bool> (K True)" unfolding \<nu>Equalable_def NuBool_def by auto

end